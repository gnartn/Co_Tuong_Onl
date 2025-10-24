# main.py
from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from fastapi.responses import FileResponse, JSONResponse
from fastapi.staticfiles import StaticFiles
import json, asyncio, sqlite3, time, uuid, copy, traceback
import uvicorn  # <-- THÊM MỚI
import os       # <-- THÊM MỚI

app = FastAPI()
app.mount("/static", StaticFiles(directory="static"), name="static")

# Tạo đường dẫn lưu database (hoạt động trên cả Render và máy local)
DATA_DIR = os.environ.get('DATA_DIR', '.')
DB_PATH = os.path.join(DATA_DIR, 'games.db')

# ------------------ Database init ------------------
def init_db():
    conn = sqlite3.connect(DB_PATH)
    c = conn.cursor()
    c.execute("""
    CREATE TABLE IF NOT EXISTS games (
        id TEXT PRIMARY KEY,
        room TEXT,
        player_red TEXT,
        player_black TEXT,
        start_ts INTEGER,
        end_ts INTEGER,
        winner TEXT
    )
    """)
    c.execute("""
    CREATE TABLE IF NOT EXISTS moves (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        game_id TEXT,
        move_index INTEGER,
        from_x INTEGER, from_y INTEGER,
        to_x INTEGER, to_y INTEGER,
        piece TEXT,
        ts INTEGER
    )
    """)
    conn.commit()
    conn.close()

init_db()

# ------------------ In-memory structures ------------------
lobby = {}                # { websocket: player_name }
rooms = {}                # { room_id: {...} }
player_room_map = {}      # { websocket: room_id }
pending_challenges = {}   # { target_name: challenger_name }
pending_challenge_targets = {}  # { challenger_name: target_name }
lock = asyncio.Lock()

# ------------------ Game logic helpers ------------------
def init_board():
    board = [["" for _ in range(9)] for _ in range(10)]
    board[0] = ['車','馬','象','士','將','士','象','馬','車']
    board[2] = ['', '砲', '', '', '', '', '', '砲', '']
    board[3] = ['卒', '', '卒', '', '卒', '', '卒', '', '卒']
    board[9] = ['俥', '傌', '相', '仕', '帥', '仕', '相', '傌', '俥']
    board[7] = ['', '炮', '', '', '', '', '', '炮', '']
    board[6] = ['兵', '', '兵', '', '兵', '', '兵', '', '兵']
    return {"board": board}

def get_color(piece: str) -> str:
    if piece in ['俥','傌','相','仕','帥','炮','兵']: return 'red'
    if piece in ['車','馬','象','士','將','砲','卒']: return 'black'
    return 'none'

def get_opponent_color(color: str) -> str:
    return 'black' if color == 'red' else 'red'

def is_in_palace(x: int, y: int, color: str) -> bool:
    if not (3 <= x <= 5): return False
    if color == 'red' and (7 <= y <= 9): return True
    if color == 'black' and (0 <= y <= 2): return True
    return False

def find_king(board, color: str):
    king_piece = '帥' if color == 'red' else '將'
    for y in range(10):
        for x in range(9):
            if board[y][x] == king_piece:
                return (x, y)
    return (-1, -1)

def count_blockers(board, fx, fy, tx, ty) -> int:
    count = 0
    if fx == tx:
        step = 1 if ty > fy else -1
        for y in range(fy + step, ty, step):
            if board[y][fx] != "": count += 1
    elif fy == ty:
        step = 1 if tx > fx else -1
        for x in range(fx + step, tx, step):
            if board[fy][x] != "": count += 1
    return count

def _is_legal_chariot(board, fx, fy, tx, ty):
    return (fx == tx or fy == ty) and count_blockers(board, fx, fy, tx, ty) == 0

def _is_legal_horse(board, fx, fy, tx, ty):
    dx, dy = abs(tx - fx), abs(ty - fy)
    if not ((dx == 1 and dy == 2) or (dx == 2 and dy == 1)): return False
    if dx == 2:
        if board[fy][(fx + tx)//2] != "": return False
    else:
        if board[(fy + ty)//2][fx] != "": return False
    return True

def _is_legal_elephant(board, fx, fy, tx, ty, color):
    if not (abs(tx - fx) == 2 and abs(ty - fy) == 2): return False
    if (color == 'red' and ty < 5) or (color == 'black' and ty > 4): return False
    if board[(fy + ty)//2][(fx + tx)//2] != "": return False
    return True

def _is_legal_advisor(board, fx, fy, tx, ty, color):
    return abs(tx - fx) == 1 and abs(ty - fy) == 1 and is_in_palace(tx, ty, color)

def _is_legal_general(board, fx, fy, tx, ty, color):
    return (abs(tx - fx) + abs(ty - fy) == 1) and is_in_palace(tx, ty, color)

def _is_legal_cannon(board, fx, fy, tx, ty, target_piece):
    if not (fx == tx or fy == ty): return False
    blockers = count_blockers(board, fx, fy, tx, ty)
    if target_piece == "":
        return blockers == 0
    else:
        return blockers == 1

def _is_legal_soldier(board, fx, fy, tx, ty, color):
    dx, dy = abs(tx - fx), abs(ty - fy)
    if not (dx + dy == 1): return False
    if color == 'red':
        if ty > fy: return False
        if fy >= 5 and tx != fx: return False
    else:
        if ty < fy: return False
        if fy <= 4 and tx != fx: return False
    return True

def is_legal_move_for_piece(board, fx, fy, tx, ty):
    piece = board[fy][fx]
    color = get_color(piece)
    target_piece = board[ty][tx]
    if piece in ['俥','車']: return _is_legal_chariot(board, fx, fy, tx, ty)
    if piece in ['傌','馬']: return _is_legal_horse(board, fx, fy, tx, ty)
    if piece in ['相','象']: return _is_legal_elephant(board, fx, fy, tx, ty, color)
    if piece in ['仕','士']: return _is_legal_advisor(board, fx, fy, tx, ty, color)
    if piece in ['帥','將']: return _is_legal_general(board, fx, fy, tx, ty, color)
    if piece in ['炮','砲']: return _is_legal_cannon(board, fx, fy, tx, ty, target_piece)
    if piece in ['兵','卒']: return _is_legal_soldier(board, fx, fy, tx, ty, color)
    return False

def is_square_attacked(board, x, y, attacker_color):
    for fy in range(10):
        for fx in range(9):
            piece = board[fy][fx]
            if get_color(piece) == attacker_color:
                if is_legal_move_for_piece(board, fx, fy, x, y):
                    return True
    return False

def is_king_in_check(board, color):
    kx, ky = find_king(board, color)
    if kx == -1: return False
    return is_square_attacked(board, kx, ky, get_opponent_color(color))

def is_flying_general(board):
    rx, ry = find_king(board, 'red')
    bx, by = find_king(board, 'black')
    if rx == -1 or bx == -1: return False
    if rx != bx: return False
    if count_blockers(board, rx, ry, bx, by) == 0: return True
    return False

def apply_move(state, move):
    fx, fy = move["from"]["x"], move["from"]["y"]
    tx, ty = move["to"]["x"], move["to"]["y"]
    piece = state["board"][fy][fx]
    state["board"][fy][fx] = ""
    state["board"][ty][tx] = piece

def is_valid_move(board, move, player_color):
    fx, fy = move["from"]["x"], move["from"]["y"]
    tx, ty = move["to"]["x"], move["to"]["y"]

    if not (0 <= fx < 9 and 0 <= fy < 10 and 0 <= tx < 9 and 0 <= ty < 10):
        return False, "Đi ra ngoài bàn cờ"
    piece = board[fy][fx]
    if piece == "": return False, "Ô trống, không có quân"
    if get_color(piece) != player_color: return False, "Không phải quân của bạn"
    target_piece = board[ty][tx]
    if target_piece != "" and get_color(target_piece) == player_color:
        return False, "Không thể ăn quân mình"
    if not is_legal_move_for_piece(board, fx, fy, tx, ty):
        return False, "Nước đi không hợp lệ"

    temp_board = copy.deepcopy(board)
    temp_board[ty][tx] = temp_board[fy][fx]
    temp_board[fy][fx] = ""

    if is_flying_general(temp_board): return False, "Lộ tướng!"

    return True, ""

# ------------------ DB helpers ------------------
def create_game_record(room_id, player_red, player_black):
    gid = str(uuid.uuid4())
    ts = int(time.time())
    try:
        conn = sqlite3.connect(DB_PATH)
        c = conn.cursor()
        c.execute("INSERT INTO games(id, room, player_red, player_black, start_ts) VALUES (?,?,?,?,?)",
                  (gid, room_id, player_red, player_black, ts))
        conn.commit()
        conn.close()
        return gid
    except Exception as e:
        print(f"[DB] Error create_game_record: {e}")
        return None

def add_move_record(game_id, idx, fx, fy, tx, ty, piece):
    ts = int(time.time())
    try:
        conn = sqlite3.connect(DB_PATH)
        c = conn.cursor()
        c.execute("INSERT INTO moves(game_id, move_index, from_x, from_y, to_x, to_y, piece, ts) VALUES (?,?,?,?,?,?,?,?)",
                  (game_id, idx, fx, fy, tx, ty, piece, ts))
        conn.commit()
        conn.close()
    except Exception as e:
        print(f"[DB] Error add_move_record: {e}")

def finish_game_record(game_id, winner):
    if not game_id: return
    ts = int(time.time())
    try:
        conn = sqlite3.connect(DB_PATH)
        c = conn.cursor()
        c.execute("UPDATE games SET end_ts=?, winner=? WHERE id=?", (ts, winner, game_id))
        conn.commit()
        conn.close()
    except Exception as e:
        print(f"[DB] Error finish_game_record: {e}")

# ------------------ Core send/broadcast helpers ------------------
async def broadcast_to_room(room_id: str, message: dict, exclude_ws: WebSocket = None):
    if room_id not in rooms: return
    msg = json.dumps(message, ensure_ascii=False)
    tasks = []
    for ws in list(rooms[room_id]["players"].keys()):
        if ws == exclude_ws: continue
        try:
            tasks.append(ws.send_text(msg))
        except Exception:
            pass
    if tasks:
        await asyncio.gather(*tasks, return_exceptions=True)

async def broadcast_to_lobby(message: dict, exclude_ws: WebSocket = None):
    msg = json.dumps(message, ensure_ascii=False)
    tasks = []
    for ws in list(lobby.keys()):
        if ws == exclude_ws: continue
        try:
            tasks.append(ws.send_text(msg))
        except Exception:
            pass
    if tasks:
        await asyncio.gather(*tasks, return_exceptions=True)

async def send_lobby_update():
    players = list(lobby.values())
    dead_clients = []
    for ws, name in list(lobby.items()):
        try:
            await ws.send_text(json.dumps({"type": "lobby_update", "players": players}, ensure_ascii=False))
        except Exception as e:
            print(f"[WARN] Không gửi được cho {name}: {e}")
            dead_clients.append(ws)
    for ws in dead_clients:
        lobby.pop(ws, None)
    print(f"[LOBBY] Hiện có {len(players)} người: {', '.join(players) if players else 'Sảnh trống.'}")

async def send_state(room_id: str):
    if room_id not in rooms: return
    game = rooms[room_id]
    state_to_send = {
        "type": "state",
        "turn": game["turn"],
        "state": game["state"],
        "colors": game["player_colors"],
        "clocks": game.get("clocks", {"red": 300, "black": 300})
    }
    await broadcast_to_room(room_id, state_to_send)

async def send_game_over(room_id, winner, reason):
    if room_id not in rooms: return
    game = rooms[room_id]
    if game.get("timer_task"):
        try:
            game["timer_task"].cancel()
        except:
            pass
        game["timer_task"] = None

    if game.get("game_id"):
        finish_game_record(game["game_id"], winner)

    game["game_id"] = None
    game["rematch_offered_by"] = None

    msg = {"type": "game_over", "winner": winner, "reason": reason}
    await broadcast_to_room(room_id, msg)

# ------------------ Timer loop ------------------
async def timer_loop(room_id: str):
    print(f"[TIMER] Starting for room {room_id}")
    try:
        while True:
            await asyncio.sleep(1)
            async with lock:
                if room_id not in rooms:
                    break
                game = rooms[room_id]
                if game.get("game_id") is None:
                    continue
                turn = game["turn"]
                game["clocks"][turn] -= 1
                await broadcast_to_room(room_id, {"type": "clock_update", "clocks": game["clocks"]})
                if game["clocks"][turn] <= 0:
                    winner = get_opponent_color(turn)
                    reason = f"{turn} hết giờ"
                    print(f"[TIMER] Room {room_id} - {turn} ran out. Winner: {winner}")
                    await send_game_over(room_id, winner, reason)
                    break
    except asyncio.CancelledError:
        print(f"[TIMER] Cancelled for room {room_id}")
    except Exception as e:
        print(f"[TIMER] Error for room {room_id}: {e}")
        traceback.print_exc()
        async with lock:
            if room_id in rooms:
                rooms[room_id]["timer_task"] = None

# ------------------ Cleanup on disconnect or leave ------------------
async def cleanup_player(ws: WebSocket):
    async with lock:
        if ws in lobby:
            name = lobby.pop(ws)
            print(f"[CLEANUP] Lobby player '{name}' disconnected/left.")
            await send_lobby_update()
            pending_challenges.pop(name, None)
            pending_challenge_targets.pop(name, None)
            return

        if ws in player_room_map:
            room_id = player_room_map.pop(ws)
            if room_id in rooms:
                game = rooms[room_id]
                name = game["players"].pop(ws, None)
                if name:
                    color = game["player_colors"].get(name)
                    if color in ("red", "black") and game.get("game_id"):
                        winner = get_opponent_color(color)
                        reason = f"{name} ({color}) đã ngắt kết nối"
                        print(f"[CLEANUP] Player {name} disconnected in room {room_id}. Winner: {winner}")
                        await send_game_over(room_id, winner, reason)
                    else:
                        await broadcast_to_room(room_id, {"type":"system","text": f"{name} đã rời phòng."}, exclude_ws=ws)

                if not game["players"]:
                    print(f"[CLEANUP] Room {room_id} is empty. Deleting.")
                    if game.get("timer_task"):
                        try: game["timer_task"].cancel()
                        except: pass
                    del rooms[room_id]

            pending_challenges.pop(name, None)
            pending_challenge_targets.pop(name, None)

# ------------------ Utilities to find sockets by name ------------------
def find_player_in_lobby(player_name: str):
    for ws, name in lobby.items():
        if name == player_name:
            return ws
    return None

def find_ws_by_name(player_name: str):
    ws = find_player_in_lobby(player_name)
    if ws: return ws
    for room in rooms.values():
        for w, n in room["players"].items():
            if n == player_name:
                return w
    return None

def get_opponent_ws(room_id: str, self_ws: WebSocket):
    if room_id not in rooms: return None
    for ws in rooms[room_id]["players"]:
        if ws != self_ws:
            return ws
    return None

# ------------------ HTTP routes ------------------
@app.get("/")
async def index():
    # --- ĐÂY LÀ DÒNG ĐÃ SỬA ---
    return FileResponse("client_web.html")

@app.get("/leaderboard")
async def leaderboard():
    try:
        conn = sqlite3.connect(DB_PATH)
        c = conn.cursor()
        c.execute("SELECT winner, COUNT(*) FROM games WHERE winner IS NOT NULL GROUP BY winner ORDER BY COUNT(*) DESC")
        rows = c.fetchall()
        conn.close()
        return JSONResponse([{"player": r[0], "wins": r[1]} for r in rows])
    except Exception as e:
        print(f"[DB] leaderboard error: {e}")
        return JSONResponse([])

# ------------------ WebSocket endpoint ------------------
@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    await websocket.accept()
    player_name = None
    current_room_id = None

    try:
        while True:
            data = await websocket.receive_text()
            try:
                msg = json.loads(data)
            except Exception:
                await websocket.send_text(json.dumps({"type":"error","reason":"invalid_json"}))
                continue

            msg_type = msg.get("type")

            # ---------- JOIN LOBBY ----------
            if msg_type == "join_lobby":
                player_name = msg.get("player") or ("P"+str(int(time.time())%1000))
                async with lock:
                    lobby[websocket] = player_name
                print(f"[LOBBY] {player_name} joined lobby.")
                await websocket.send_text(json.dumps({"type":"system","text":f"Chào mừng {player_name} đến sảnh."}, ensure_ascii=False))
                await send_lobby_update()
                continue

            # ---------- CHALLENGE ----------
            if msg_type == "challenge":
                target_name = msg.get("target_player")
                if not player_name: continue
                if target_name == player_name:
                    await websocket.send_text(json.dumps({"type":"error","reason":"Bạn không thể tự thách đấu mình."}, ensure_ascii=False))
                    continue

                async with lock:
                    target_ws = find_player_in_lobby(target_name)
                    if not target_ws:
                        await websocket.send_text(json.dumps({"type":"error","reason":f"Không tìm thấy người chơi '{target_name}' trong sảnh."}, ensure_ascii=False))
                        continue

                    pending_challenges[target_name] = player_name
                    pending_challenge_targets[player_name] = target_name

                    try:
                        await target_ws.send_text(json.dumps({"type":"challenge_received", "from_player": player_name}, ensure_ascii=False))
                    except Exception as e:
                        print(f"[CHALLENGE] Failed to send to {target_name}: {e}")
                        await websocket.send_text(json.dumps({"type":"error","reason":"Không thể gửi lời mời, đối thủ không phản hồi."}, ensure_ascii=False))
                        pending_challenges.pop(target_name, None)
                        pending_challenge_targets.pop(player_name, None)
                        continue

                print(f"[CHALLENGE] {player_name} -> {target_name}")
                await websocket.send_text(json.dumps({"type":"system","text":f"Đã gửi lời mời đến {target_name}. Đang chờ đối thủ chấp nhận..."}))
                continue

            # ---------- CHALLENGE ACCEPT ----------
            if msg_type == "challenge_accept":
                opponent_name = msg.get("opponent_name")
                if not player_name: continue

                async with lock:
                    challenger_ws = find_ws_by_name(opponent_name)

                    if not challenger_ws and pending_challenges.get(player_name) == opponent_name:
                        challenger_ws = find_player_in_lobby(opponent_name)

                    if not challenger_ws:
                        await websocket.send_text(json.dumps({"type":"error","reason":f"'{opponent_name}' không còn ở sảnh hoặc phiên đã lỗi."}, ensure_ascii=False))
                        continue

                    pending_challenges.pop(player_name, None)
                    pending_challenge_targets.pop(opponent_name, None)
                    pending_challenges.pop(opponent_name, None)
                    pending_challenge_targets.pop(player_name, None)

                    if websocket in lobby: del lobby[websocket]
                    if challenger_ws in lobby: del lobby[challenger_ws]

                    room_id = str(uuid.uuid4())
                    player_room_map[websocket] = room_id
                    player_room_map[challenger_ws] = room_id

                    challenger_name = None
                    for w, n in list(lobby.items()):
                        if w == challenger_ws:
                            challenger_name = n
                            break
                    if not challenger_name:
                        challenger_name = opponent_name

                    acceptor_name = player_name

                    game_id = create_game_record(room_id, challenger_name, acceptor_name)
                    rooms[room_id] = {
                        "players": {websocket: acceptor_name, challenger_ws: challenger_name},
                        "player_colors": {challenger_name: 'red', acceptor_name: 'black'},
                        "turn": "red",
                        "state": init_board(),
                        "game_id": game_id,
                        "move_count": 0,
                        "clocks": {"red": 300, "black": 300},
                        "timer_task": None,
                        "rematch_offered_by": None
                    }

                    rooms[room_id]["timer_task"] = asyncio.create_task(timer_loop(room_id))

                    await websocket.send_text(json.dumps({"type": "game_start", "room_id": room_id, "color": "black", "opponent": challenger_name}, ensure_ascii=False))
                    await challenger_ws.send_text(json.dumps({"type": "game_start", "room_id": room_id, "color": "red", "opponent": acceptor_name}, ensure_ascii=False))

                    print(f"[MATCH START] room={room_id} {challenger_name}(red) vs {acceptor_name}(black)")

                    await send_state(room_id)

                await send_lobby_update()
                continue

            # ---------- CHALLENGE DECLINE ----------
            if msg_type == "challenge_decline":
                opponent_name = msg.get("opponent_name")
                async with lock:
                    challenger_ws = find_ws_by_name(opponent_name)
                    if challenger_ws:
                        try:
                            await challenger_ws.send_text(json.dumps({"type":"system", "text": f"{player_name} đã từ chối lời mời."}, ensure_ascii=False))
                        except:
                            pass
                    pending_challenges.pop(player_name, None)
                    pending_challenge_targets.pop(opponent_name, None)
                continue

            # ---------- MOVE ----------
            if msg_type == "move":
                move = msg.get("move")
                room_id = player_room_map.get(websocket)
                if not room_id or room_id not in rooms:
                    await websocket.send_text(json.dumps({"type":"error","reason":"Bạn không ở trong phòng."}, ensure_ascii=False))
                    continue

                is_check_alert = False

                async with lock:
                    game = rooms[room_id]
                    player = game["players"].get(websocket)
                    if not player: continue

                    player_color = game["player_colors"].get(player, "spectator")
                    if player_color != game["turn"]:
                        await websocket.send_text(json.dumps({"type":"error","reason":"Không phải lượt của bạn"}, ensure_ascii=False))
                        continue

                    if game.get("game_id") is None:
                        await websocket.send_text(json.dumps({"type":"error","reason":"Game đã kết thúc"}, ensure_ascii=False))
                        continue

                    valid, reason = is_valid_move(game["state"]["board"], move, player_color)
                    if not valid:
                        await websocket.send_text(json.dumps({"type":"error","reason":reason}, ensure_ascii=False))
                        continue

                    fx, fy = move["from"]["x"], move["from"]["y"]
                    piece = game["state"]["board"][fy][fx]
                    apply_move(game["state"], move)

                    opponent_color = get_opponent_color(player_color)
                    if is_king_in_check(game["state"]["board"], opponent_color):
                        is_check_alert = True

                    idx = game.get("move_count", 0) + 1
                    add_move_record(game["game_id"], idx, fx, fy, move["to"]["x"], move["to"]["y"], piece)
                    game["move_count"] = idx

                    game["turn"] = opponent_color

                    red_king = find_king(game["state"]["board"], 'red')[0] != -1
                    black_king = find_king(game["state"]["board"], 'black')[0] != -1

                    if not red_king or not black_king:
                        winner = 'red' if red_king and not black_king else 'black'
                        reason_msg = "Tướng đã bị ăn"
                        await send_game_over(room_id, winner, reason_msg)
                        continue

                await send_state(room_id)
                if is_check_alert:
                    await broadcast_to_room(room_id, {"type":"system", "text": "CHIẾU TƯỚNG!"})
                continue

            # ---------- OFFER REMATCH ----------
            if msg_type == "offer_rematch":
                room_id = player_room_map.get(websocket)
                if not room_id or room_id not in rooms: continue

                async with lock:
                    game = rooms[room_id]
                    if game.get("game_id") is not None:
                        await websocket.send_text(json.dumps({"type":"error","reason":"Game chưa kết thúc"}))
                        continue

                    player = game["players"].get(websocket)

                    if game["rematch_offered_by"] and game["rematch_offered_by"] != player:
                        print(f"[{room_id}] Chấp nhận chơi lại (cả 2 cùng mời)")
                        p1, p2 = list(game["player_colors"].keys())
                        game_id = create_game_record(room_id, p1, p2)

                        game["state"] = init_board()
                        game["turn"] = "red"
                        game["move_count"] = 0
                        game["game_id"] = game_id
                        game["clocks"] = {"red": 300, "black": 300}
                        game["rematch_offered_by"] = None
                        game["timer_task"] = asyncio.create_task(timer_loop(room_id))

                        await send_state(room_id)
                        await broadcast_to_room(room_id, {"type":"system", "text": "Cả hai đã đồng ý. Trận đấu mới bắt đầu!"})

                    else:
                        game["rematch_offered_by"] = player
                        opponent_ws = get_opponent_ws(room_id, websocket)
                        if opponent_ws:
                            try:
                                await opponent_ws.send_text(json.dumps({"type":"rematch_offered", "from": player}, ensure_ascii=False))
                            except:
                                pass
                        await websocket.send_text(json.dumps({"type":"system", "text": "Đã gửi lời mời chơi lại."}, ensure_ascii=False))
                continue

            # ---------- LEAVE_GAME ----------
            if msg_type == "leave_game":
                room_id = player_room_map.get(websocket)
                if not room_id or room_id not in rooms:
                    # If in lobby, nothing to do
                    async with lock:
                        if websocket not in lobby and player_name:
                            lobby[websocket] = player_name
                            await send_lobby_update()
                    continue

                await cleanup_player(websocket)
                async with lock:
                    lobby[websocket] = player_name
                await websocket.send_text(json.dumps({"type":"system","text":"Đã quay về sảnh."}, ensure_ascii=False))
                await send_lobby_update()
                continue

            # ---------- unknown ----------
            await websocket.send_text(json.dumps({"type":"error","reason":"unknown_message_type"}))

    except WebSocketDisconnect:
        print(f"[WS] Disconnect: {player_name}")
        await cleanup_player(websocket)
    except Exception as e:
        print(f"[WS] Exception for {player_name}: {e}")
        traceback.print_exc()
        await cleanup_player(websocket)

# --- ĐÂY LÀ PHẦN CODE MỚI THÊM VÀO CUỐI FILE ---
# Nó cho phép bạn chạy file bằng lệnh `python main.py`
# và tự động lấy PORT từ môi trường (như Render)
if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8000))
    print(f"--- Starting server on 0.0.0.0:{port} ---")
    uvicorn.run(app, host="0.0.0.0", port=port)