#!/usr/bin/env python3
"""
Adaptive BB30-3.2 Live Monitor — WebSocket Edition
- Real-time 30m klines via Binance WebSocket (instant signals)
- Real-time 1m klines for TP/SL checks
- Real-time ticker prices for dashboard
- 1h SMA50 trend filter
"""
import json, os, time, math, threading, asyncio
from http.server import HTTPServer, SimpleHTTPRequestHandler
from urllib.parse import urlparse
from datetime import datetime
import websocket
import websockets

PAIRS = ["ETHUSDT", "SOLUSDT", "DOGEUSDT"]
TIMEFRAMES = {"30m": 1800}
BALANCE_INIT = 100.0
LEVERAGE = 125
BASE_POSITION_PCT = 0.40
TP_PCT = 0.005       # 0.5% for against/no-trend
TP_ALIGNED_PCT = 0.008  # 0.8% for aligned
SL_PCT = 0.004       # 0.4% uniform SL (1.25:1 R:R)
BB_PERIOD = 30
BB_STD = 3.2
DASHBOARD_PORT = int(os.environ.get("PORT", 8766))
POLL_INTERVAL = 60
# BB(30,3.2) is mean-reversion: against-trend signals outperform
POS_MULT_ALIGNED = 0.3
POS_MULT_AGAINST = 1.0
POS_MULT_NO_TREND = 0.5
CONSECUTIVE_LOSS_LIMIT = 3
PAUSE_DURATION = 7200  # 2h pause after 3 losses
DAILY_LOSS_LIMIT_PCT = -10.0  # stop after -10% daily drawdown

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(BASE_DIR, "data")
os.makedirs(DATA_DIR, exist_ok=True)
ACCOUNT_FILE = os.path.join(DATA_DIR, "account.json")
SIGNAL_LOG = os.path.join(DATA_DIR, "signals.log")
TRADE_LOG = os.path.join(DATA_DIR, "trades.json")
STATE_FILE = os.path.join(DATA_DIR, "state.json")
TREND_CACHE_FILE = os.path.join(DATA_DIR, "trend_cache.json")
LAST_SIGNAL_FILE = os.path.join(DATA_DIR, "last_signal.json")
DASHBOARD_DIR = os.path.join(BASE_DIR, "dashboard")

# ─── WebSocket Shared State ───
ws_lock = threading.Lock()
ws_klines_30m = {}  # {pair: [kline,...]}
ws_klines_1m = {}   # {pair: [kline,...]}
ws_klines_1h = {}   # {pair: [kline,...]}
ws_prices = {}      # {pair: {price, change}}
ws_trend = {}       # {pair: "LONG"/"SHORT"}
ws_sma50 = {}       # {pair: float}
ws_signal = {}      # {pair: signal dict or None}
ws_last_signal = {} # persistent cache of last signal (for market API)
try:
    with open(LAST_SIGNAL_FILE) as f: ws_last_signal = json.load(f)
except: ws_last_signal = {}
ws_market_cache = {} # merged cache for /api/market
ws_last_30m_ts = {} # {pair: last processed 30m candle close timestamp}
ws_connected = False

# ─── Helpers ───

def log(msg):
    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    print(f"[{ts}] {msg}", flush=True)

def mac_notify(title, msg, subtitle=""):
    try:
        s = f'display notification "{msg}" with title "{title}"'
        if subtitle: s += f' subtitle "{subtitle}"'
        s += ' sound name "default"'
        os.system(f"osascript -e '{s}' 2>/dev/null")
    except: pass

def sma(data, p):
    return sum(data[-p:])/p if len(data) >= p else None

def stdev(data, p):
    m = sma(data, p)
    return math.sqrt(sum((x-m)**2 for x in data[-p:])/p) if m else None

def compute_bb(closes):
    m, s = sma(closes, BB_PERIOD), stdev(closes, BB_PERIOD)
    if not m or not s: return None
    return {"upper": m + BB_STD*s, "mid": m, "lower": m - BB_STD*s}

def detect_signal(klines):
    if len(klines) < BB_PERIOD + 2: return None
    closes = [k["c"] for k in klines]
    bb = compute_bb(closes)
    if not bb: return None
    last, prev = klines[-1], klines[-2]
    if last["l"] <= bb["lower"] and prev["l"] > bb["lower"]:
        return {"type": "BB_LONG", "price": last["c"], "dir": "LONG", "label": "Long Entry"}
    if last["h"] >= bb["upper"] and prev["h"] < bb["upper"]:
        return {"type": "BB_SHORT", "price": last["c"], "dir": "SHORT", "label": "Short Entry"}
    return None

def get_pos_mult(signal_dir, trend_dir):
    if not trend_dir: return POS_MULT_NO_TREND
    if signal_dir == trend_dir: return POS_MULT_ALIGNED
    return POS_MULT_AGAINST

# ─── Account ───

def load_account():
    try:
        with open(ACCOUNT_FILE) as f: return json.load(f)
    except:
        return {"balance": BALANCE_INIT, "initial_balance": BALANCE_INIT,
                "equity": BALANCE_INIT, "open_trades": [],
                "closed_trades": [], "total_trades": 0,
                "wins": 0, "losses": 0, "day_pnl": 0,
                "day_date": datetime.now().strftime("%Y-%m-%d"),
                "signal_ids": [], "consecutive_losses": 0,
                "paused_until": 0}

def save_account(acc):
    with open(ACCOUNT_FILE, "w") as f: json.dump(acc, f, indent=2, default=str)

def reset_daily(acc):
    today = datetime.now().strftime("%Y-%m-%d")
    if acc["day_date"] != today:
        acc["day_pnl"] = 0; acc["day_date"] = today
    return acc

# ─── Trade Logic ───

def ts_now(): return int(time.time())

def enter_trade(acc, pair, direction, entry_price, signal_type, signal_ts, trend_dir):
    sig_id = f"{pair}_{direction}_{signal_ts}"
    if sig_id in acc["signal_ids"]: return acc
    pos_mult = get_pos_mult(direction, trend_dir)
    effective_pp = BASE_POSITION_PCT * pos_mult

    # Intelligent sizing: use remaining free balance, not full balance
    margin_used = sum(t["size"] for t in acc["open_trades"] if t["result"] is None)
    free_balance = max(0, acc["balance"] - margin_used)
    pos_size = free_balance * effective_pp
    if pos_size <= 0: return acc
    if pos_size < 0.01: return acc  # dust guard
    tp_pct = TP_ALIGNED_PCT if (trend_dir and direction == trend_dir) else TP_PCT
    sl_pct = SL_PCT
    notional = pos_size * LEVERAGE
    sl_price = entry_price * (1 - sl_pct) if direction == "LONG" else entry_price * (1 + sl_pct)
    tp_price = entry_price * (1 + tp_pct) if direction == "LONG" else entry_price * (1 - tp_pct)
    
    align_label = "ALIGNED" if (trend_dir and direction == trend_dir) else "AGAINST" if trend_dir else "NO_TREND"
    trade = {
        "sig_id": sig_id, "pair": pair, "direction": direction,
        "entry_price": entry_price, "size": round(pos_size, 2),
        "notional": round(notional, 2), "leverage": LEVERAGE,
        "entry_time": datetime.fromtimestamp(signal_ts).strftime("%Y-%m-%d %H:%M:%S"),
        "entry_ts": signal_ts,
        "tp_price": tp_price, "tp_pct": round(tp_pct*100, 2),
        "sl_price": sl_price, "sl_pct": round(sl_pct*100, 2),
        "signal_type": signal_type, "trend": trend_dir or "N/A",
        "alignment": align_label, "pos_mult": pos_mult,
        "result": None, "exit_price": None, "exit_time": None,
        "pnl": None, "pnl_pct": None, "exit_reason": None,
    }
    acc["open_trades"].append(trade)
    acc["total_trades"] += 1
    acc["signal_ids"].append(sig_id)
    emoji = "🚀" if align_label == "ALIGNED" else "📡" if align_label == "NO_TREND" else "⚠️"
    log(f"{emoji} {pair} {direction} @ ${entry_price:.2f} [{align_label}] "
        f"TP={tp_pct*100:.1f}% pos=${pos_size:.2f} ({effective_pp*100:.0f}% of free=${free_balance:.2f}) sl={sl_pct*100:.1f}%")
    msg = (f"{pair} {direction} ({align_label})\n"
           f"Entry: ${entry_price:.2f}\nTP: ${tp_price:.2f}\nSL: ${sl_price:.2f}\n"
           f"Size: {effective_pp*100:.0f}% = ${pos_size:.2f} | {LEVERAGE}x")
    mac_notify(f"{emoji} {pair} {direction}", msg, f"{align_label}")
    broadcast_all("trade_enter")
    return acc

def close_trade(acc, trade, exit_price, reason, exit_ts=None):
    if trade["result"] is not None: return acc
    if exit_ts is None: exit_ts = ts_now()
    direction = trade["direction"]; entry = trade["entry_price"]
    notional = trade["notional"]
    dm = 1 if direction == "LONG" else -1
    pnl_pct = dm * (exit_price - entry) / entry * 100
    pnl = notional * (exit_price - entry) / entry
    trade.update({"exit_price": exit_price,
        "exit_time": datetime.fromtimestamp(exit_ts).strftime("%Y-%m-%d %H:%M:%S"),
        "pnl": round(pnl, 2), "pnl_pct": round(pnl_pct, 2),
        "result": "WIN" if pnl > 0 else "LOSS", "exit_reason": reason})
    acc["balance"] = round(acc["balance"] + pnl, 2)
    if pnl > 0:
        acc["wins"] += 1
        acc["consecutive_losses"] = 0
    else:
        acc["losses"] += 1
        acc["consecutive_losses"] = acc.get("consecutive_losses", 0) + 1
        if acc["consecutive_losses"] >= CONSECUTIVE_LOSS_LIMIT:
            acc["paused_until"] = ts_now() + PAUSE_DURATION
            log(f"⏸️ {CONSECUTIVE_LOSS_LIMIT} consecutive losses — paused 2h")
            mac_notify("⏸️ Strategy Paused", f"{CONSECUTIVE_LOSS_LIMIT} losses in a row", "Resuming in 2h")
    acc["day_pnl"] = round(acc["day_pnl"] + pnl, 2)
    icon = "✅" if pnl > 0 else "❌"
    log(f"{icon} {trade['pair']} {trade['direction']} @${exit_price:.2f} "
        f"PnL=${pnl:.2f} ({pnl_pct:+.2f}%) [{reason}] Bal=${acc['balance']:.2f}")
    mac_notify(f"{icon} {trade['pair']}", f"PnL: ${pnl:.2f} ({pnl_pct:+.2f}%)\n"
               f"Balance: ${acc['balance']:.2f}\nReason: {reason}", trade['alignment'])
    broadcast_all("trade_close")
    with open(SIGNAL_LOG, "a") as f:
        f.write(f"[{trade['entry_time']}] {trade['pair']} {trade['direction']} "
                f"${trade['entry_price']:.2f}->${exit_price:.2f} PnL=${pnl:.2f} ({pnl_pct:+.2f}%) [{reason}]\n")
    return acc

# ─── WebSocket Manager ───

def build_ws_url():
    streams = []
    for p in PAIRS:
        low = p.lower()
        streams.append(f"{low}@kline_30m")
        streams.append(f"{low}@kline_1m")
        streams.append(f"{low}@kline_1h")
        streams.append(f"{low}@ticker")
    return f"wss://fstream.binance.com/stream?streams={'/'.join(streams)}"

def handle_ws_message(ws, message):
    global ws_klines_30m, ws_klines_1m, ws_klines_1h, ws_prices
    global ws_trend, ws_sma50, ws_signal, ws_last_30m_ts, ws_market_cache
    try:
        msg = json.loads(message)
        if msg.get("stream"):
            data = msg["data"]
            pair = data["s"]
            e_type = data.get("e", "")

            if e_type == "kline":
                k = data["k"]
                tf = k["i"]
                kline = {"t": k["t"]//1000, "o": float(k["o"]), "h": float(k["h"]),
                         "l": float(k["l"]), "c": float(k["c"]), "v": float(k["v"]),
                         "x": k["x"]}

                if tf == "30m":
                    with ws_lock:
                        if pair not in ws_klines_30m:
                            ws_klines_30m[pair] = []
                        klist = ws_klines_30m[pair]
                        if not klist or kline["t"] != klist[-1]["t"]:
                            klist.append(kline)
                        else:
                            klist[-1] = kline
                        if len(klist) > 60:
                            ws_klines_30m[pair] = klist[-50:]
                    # Signal detection on candle close
                    if kline["x"]:
                        with ws_lock:
                            klist = ws_klines_30m.get(pair, [])
                            last_ts = ws_last_30m_ts.get(pair, 0)
                            if kline["t"] > last_ts:
                                sig = detect_signal(klist)
                                ws_signal[pair] = sig
                                ws_last_30m_ts[pair] = kline["t"]

                elif tf == "1m":
                    with ws_lock:
                        if pair not in ws_klines_1m:
                            ws_klines_1m[pair] = []
                        klist = ws_klines_1m[pair]
                        if not klist or kline["t"] != klist[-1]["t"]:
                            klist.append(kline)
                        else:
                            klist[-1] = kline
                        if len(klist) > 120:
                            ws_klines_1m[pair] = klist[-60:]

                elif tf == "1h":
                    with ws_lock:
                        if pair not in ws_klines_1h:
                            ws_klines_1h[pair] = []
                        klist = ws_klines_1h[pair]
                        if not klist or kline["t"] != klist[-1]["t"]:
                            klist.append(kline)
                        else:
                            klist[-1] = kline
                        if len(klist) > 55:
                            ws_klines_1h[pair] = klist[-55:]
                    if kline["x"]:
                        with ws_lock:
                            klist = ws_klines_1h.get(pair, [])
                            if len(klist) >= 50:
                                closes = [x["c"] for x in klist]
                                s50 = sma(closes, 50)
                                if s50:
                                    ws_sma50[pair] = s50
                                    ws_trend[pair] = "LONG" if klist[-1]["c"] > s50 else "SHORT"

            elif e_type == "24hrTicker":
                with ws_lock:
                    ws_prices[pair] = {
                        "price": float(data["c"]),
                        "change": float(data["P"]),
                        "high": float(data["h"]),
                        "low": float(data["l"]),
                        "volume": float(data["v"]),
                        "priceChangePercent": float(data["P"]),
                    }
                # Instant price push to dashboard (throttled to 1s intervals)
                now = time.time()
                last = getattr(handle_ws_message, "_last_price_bcast", 0)
                if now - last >= 1.0:
                    handle_ws_message._last_price_bcast = now
                    rebuild_market_cache()

    except Exception as e:
        log(f"WS msg error: {e}")

def handle_ws_error(ws, error):
    log(f"WS error: {error}")

def handle_ws_close(ws, close_status_code, close_msg):
    global ws_connected
    ws_connected = False
    log(f"WS closed ({close_status_code}): {close_msg}")
    log("Reconnecting in 5s...")
    time.sleep(5)

def handle_ws_open(ws):
    global ws_connected
    ws_connected = True
    log("WebSocket connected — receiving real-time data")

def run_websocket():
    url = build_ws_url()
    log(f"Connecting WebSocket ({len(PAIRS)*4} streams)...")
    ws = websocket.WebSocketApp(url,
        on_message=handle_ws_message,
        on_error=handle_ws_error,
        on_close=handle_ws_close,
        on_open=handle_ws_open)
    ws.run_forever()

# ─── Rebuild Market Cache (called periodically) ───

def rebuild_market_cache():
    global ws_market_cache
    with ws_lock:
        cache = {}
        for pair in PAIRS:
            price_data = ws_prices.get(pair, {})
            price = price_data.get("price")
            if not price: continue
            klist = ws_klines_30m.get(pair, [])
            if len(klist) < BB_PERIOD: continue
            closes = [k["c"] for k in klist]
            bb = compute_bb(closes)
            trend = ws_trend.get(pair)
            sma50_val = ws_sma50.get(pair)
            sig = ws_signal.get(pair) or ws_last_signal.get(pair)
            cache[pair] = {
                "price": price,
                "change": round(price_data.get("priceChangePercent", 0), 2),
                "bb": bb,
                "trend": trend or "N/A",
                "sma50": round(sma50_val, 2) if sma50_val else None,
                "signal": sig,
            }
        if cache:
            ws_market_cache = cache
    # Broadcast outside lock to avoid deadlock with build_market_data
    broadcast_all("market")

# ─── Process pending signals ───

def process_signals(acc):
    """Check for new signals from WS data and enter trades"""
    # Circuit breakers
    if ts_now() < acc.get("paused_until", 0): return acc
    if acc.get("day_pnl", 0) <= acc.get("balance", BALANCE_INIT) * DAILY_LOSS_LIMIT_PCT / 100: return acc

    with ws_lock:
        signals = {k: v for k, v in ws_signal.items() if v is not None}
        ws_signal.clear()
        for k, v in signals.items():
            ws_last_signal[k] = v  # persist for dashboard market cache

    for pair, sig in signals.items():
        direction = sig["dir"]
        price = sig["price"]
        sig_type = sig["type"]
        closed_ts = ts_now()
        trend_dir = ws_trend.get(pair)

        # Calculate TP/SL for dashboard display
        tp_pct = TP_ALIGNED_PCT if (trend_dir and direction == trend_dir) else TP_PCT
        sig["tp_price"] = round(price * (1 + tp_pct) if direction == "LONG" else price * (1 - tp_pct), 2)
        sig["sl_price"] = round(price * (1 - SL_PCT) if direction == "LONG" else price * (1 + SL_PCT), 2)
        sig["ts"] = closed_ts

        # Log signal immediately for dashboard history
        ts_str = datetime.fromtimestamp(closed_ts).strftime("%Y-%m-%d %H:%M:%S")
        with open(SIGNAL_LOG, "a") as f:
            f.write(f"[{ts_str}] SIGNAL {pair} {direction} @ ${price:.2f} trend={trend_dir or 'N/A'}\n")

        # Enter trade
        acc = enter_trade(acc, pair, direction, price, sig_type, closed_ts, trend_dir)

    # Persist last signals to survive restarts
    with open(LAST_SIGNAL_FILE, "w") as f:
        json.dump(ws_last_signal, f, indent=2, default=str)
    return acc

def check_trades(acc):
    """Check TP/SL and expiry for open trades using 1m WS data"""
    still_open = []
    for trade in acc["open_trades"]:
        if trade["result"] is not None: continue
        pair = trade["pair"]
        entry = trade["entry_price"]
        direction = trade["direction"]
        tp_price = trade["tp_price"]
        sl_price = trade["sl_price"]

        with ws_lock:
            klist = ws_klines_1m.get(pair, [])

        # TP/SL check on 1m candles since entry
        found = None
        for k in klist:
            if k["t"] < trade["entry_ts"]: continue
            if direction == "LONG":
                if k["h"] >= tp_price:
                    found = ("TP_HIT", tp_price); break
                if k["l"] <= sl_price:
                    found = ("SL_HIT", sl_price); break
            else:
                if k["l"] <= tp_price:
                    found = ("TP_HIT", tp_price); break
                if k["h"] >= sl_price:
                    found = ("SL_HIT", sl_price); break

        if found:
            reason, price = found
            acc = close_trade(acc, trade, price, reason)
            continue

        # 1h expiry
        if ts_now() - trade["entry_ts"] >= 3600:
            with ws_lock:
                k30list = ws_klines_30m.get(pair, [])
            if k30list:
                acc = close_trade(acc, trade, k30list[-1]["c"], "EXPIRY")
            continue

        # Update unrealized PnL
        with ws_lock:
            price_data = ws_prices.get(pair, {})
            curr = price_data.get("price")
        if curr:
            dm = 1 if direction == "LONG" else -1
            trade["current_price"] = curr
            trade["unrealized_pnl"] = round(trade["notional"] * (curr - entry) / entry, 2)
        still_open.append(trade)

    acc["open_trades"] = still_open
    return acc

# ─── Dashboard HTTP Server ───

class DashboardHandler(SimpleHTTPRequestHandler):
    def do_GET(self):
        path = urlparse(self.path).path
        if path == "/api/account":
            acc = load_account(); acc = reset_daily(acc)
            acc = process_signals(acc); acc = check_trades(acc); save_account(acc)
            fpnl = calc_fpnl(acc)
            data = json.dumps({
                "balance": acc["balance"], "initial_balance": acc["initial_balance"],
                "equity": round(acc["balance"] + fpnl, 2), "unrealized_pnl": round(fpnl, 2),
                "total_trades": acc["total_trades"],
                "wins": acc["wins"], "losses": acc["losses"],
                "win_rate": round(acc["wins"]/acc["total_trades"]*100,1) if acc["total_trades"]>0 else 0,
                "open_trades": len(acc["open_trades"]), "day_pnl": acc.get("day_pnl",0),
                "leverage": LEVERAGE, "base_position": f"{BASE_POSITION_PCT*100:.0f}%",
                "open_trades_detail": [{"pair":t["pair"],"direction":t["direction"],
                    "entry_price":round(t["entry_price"],2),
                    "current_price":round(t.get("current_price",t["entry_price"]),2),
                    "unrealized_pnl":round(t.get("unrealized_pnl",0),2),
                    "entry_time":t["entry_time"],"alignment":t.get("alignment",""),
                    "tp_pct":t.get("tp_pct",""),"pos_mult":t.get("pos_mult",""),
                    "tp_price":round(t["tp_price"],2),"sl_price":round(t["sl_price"],2)}
                    for t in acc["open_trades"] if t["result"] is None],
                "closed_trades": [{"pair":t["pair"],"direction":t["direction"],
                    "entry_price":round(t["entry_price"],2),
                    "exit_price":round(t["exit_price"],2) if t.get("exit_price") else None,
                    "pnl":t.get("pnl"),"pnl_pct":t.get("pnl_pct"),
                    "result":t["result"],"entry_time":t["entry_time"],
                    "exit_time":t.get("exit_time"),"exit_reason":t.get("exit_reason"),
                    "alignment":t.get("alignment",""),"tp_pct":t.get("tp_pct","")}
                    for t in acc["closed_trades"][-50:]][::-1],
            })
            self.send_response(200); self.send_header("Content-Type","application/json")
            self.send_header("Access-Control-Allow-Origin","*"); self.end_headers()
            self.wfile.write(data.encode()); return

        if path == "/api/signals":
            try:
                with open(SIGNAL_LOG) as f: sigs = f.readlines()[-30:][::-1]
            except: sigs = []
            data = json.dumps({
                "signals": [{"text": s.strip(), "ts": s[1:20] if s.startswith("[") else ""} for s in sigs],
                "last_signal": {p: ws_last_signal.get(p) for p in PAIRS if ws_last_signal.get(p)},
            })
            self.send_response(200); self.send_header("Content-Type","application/json")
            self.send_header("Access-Control-Allow-Origin","*"); self.end_headers()
            self.wfile.write(data.encode()); return

        if path == "/api/market":
            data = json.dumps(ws_market_cache) if ws_market_cache else "{}"
            self.send_response(200); self.send_header("Content-Type","application/json")
            self.send_header("Access-Control-Allow-Origin","*"); self.end_headers()
            self.wfile.write(data.encode()); return

        if path.startswith("/api/backtest"):
            import urllib.parse
            params = urllib.parse.parse_qs(urlparse(self.path).query)
            days = int(params.get("days", [7])[0])
            days = min(max(days, 1), 365)
            threading.Thread(target=lambda: None).start()
            try:
                result = run_backtest(days)
                data = json.dumps(result)
                self.send_response(200); self.send_header("Content-Type","application/json")
                self.send_header("Access-Control-Allow-Origin","*"); self.end_headers()
                self.wfile.write(data.encode())
            except Exception as e:
                import traceback
                err = {"error": str(e), "trace": traceback.format_exc()}
                self.send_response(500); self.send_header("Content-Type","application/json")
                self.send_header("Access-Control-Allow-Origin","*"); self.end_headers()
                self.wfile.write(json.dumps(err).encode())
            return

        if path in ("/",""): path = "/bbtc12.html"
        local = os.path.join(DASHBOARD_DIR, path.lstrip("/"))
        if os.path.isfile(local):
            ext = os.path.splitext(local)[1]
            ctype = {"html":"text/html","js":"application/javascript","css":"text/css"}.get(ext.lstrip("."),"application/octet-stream")
            with open(local,"rb") as f: data = f.read()
            self.send_response(200); self.send_header("Content-Type",ctype)
            self.send_header("Access-Control-Allow-Origin","*"); self.end_headers()
            self.wfile.write(data); return
        self.send_error(404)

def run_dashboard():
    s = HTTPServer(("0.0.0.0", DASHBOARD_PORT), DashboardHandler)
    threading.Thread(target=s.serve_forever, daemon=True).start()
    log(f"Dashboard: http://localhost:{DASHBOARD_PORT}/bbtc12.html")

# ─── WebSocket Push Server (for instant dashboard updates) ───

ws_push_clients = set()
ws_push_loop = None

async def ws_push_handler(websocket):
    ws_push_clients.add(websocket)
    try:
        # Send full state immediately on connect
        acc = load_account(); acc = reset_daily(acc); acc = process_signals(acc); acc = check_trades(acc); save_account(acc)
        data = {"type": "account", **build_account_data(acc), "market": build_market_data()}
        await websocket.send(json.dumps(data))
        async for _ in websocket:
            pass  # server only pushes, client sends nothing
    except:
        pass
    finally:
        ws_push_clients.discard(websocket)

async def ws_push_server():
    async with websockets.serve(ws_push_handler, "0.0.0.0", DASHBOARD_PORT + 1):
        log(f"WS Push: ws://localhost:{DASHBOARD_PORT + 1}")
        await asyncio.Future()

def start_ws_push():
    global ws_push_loop
    ws_push_loop = asyncio.new_event_loop()
    asyncio.set_event_loop(ws_push_loop)
    ws_push_loop.run_until_complete(ws_push_server())

def enrich_trade(t):
    """Add live current_price and unrealized_pnl from latest ws_prices."""
    if t["result"] is not None: return t
    pair = t["pair"]
    with ws_lock:
        curr = ws_prices.get(pair, {}).get("price")
    if curr:
        t["current_price"] = curr
        dm = 1 if t["direction"] == "LONG" else -1
        t["unrealized_pnl"] = round(t["notional"] * (curr - t["entry_price"]) / t["entry_price"], 2)
    return t

def calc_fpnl(acc):
    """Calculate floating PnL from live prices — zero-latency."""
    total = 0.0
    for t in acc["open_trades"]:
        if t["result"] is not None: continue
        enrich_trade(t)
        if t.get("unrealized_pnl"):
            total += t["unrealized_pnl"]
    return total

def build_account_data(acc):
    fpnl = calc_fpnl(acc)
    return {
        "balance": acc["balance"], "initial_balance": acc["initial_balance"],
        "equity": round(acc["balance"] + fpnl, 2), "unrealized_pnl": round(fpnl, 2),
        "total_trades": acc["total_trades"],
        "wins": acc["wins"], "losses": acc["losses"],
        "win_rate": round(acc["wins"]/acc["total_trades"]*100,1) if acc["total_trades"]>0 else 0,
        "open_trades": len(acc["open_trades"]), "day_pnl": acc.get("day_pnl",0),
        "leverage": LEVERAGE, "base_position": f"{BASE_POSITION_PCT*100:.0f}%",
        "open_trades_detail": [{"pair":t["pair"],"direction":t["direction"],
            "entry_price":round(t["entry_price"],2),
            "current_price":round(t.get("current_price",t["entry_price"]),2),
            "unrealized_pnl":round(t.get("unrealized_pnl",0),2),
            "entry_time":t["entry_time"],"alignment":t.get("alignment",""),
            "tp_pct":t.get("tp_pct",""),"pos_mult":t.get("pos_mult",""),
            "tp_price":round(t["tp_price"],2),"sl_price":round(t["sl_price"],2)}
            for t in acc["open_trades"] if t["result"] is None],
        "closed_trades": [{"pair":t["pair"],"direction":t["direction"],
            "entry_price":round(t["entry_price"],2),
            "exit_price":round(t["exit_price"],2) if t.get("exit_price") else None,
            "pnl":t.get("pnl"),"pnl_pct":t.get("pnl_pct"),
            "result":t["result"],"entry_time":t["entry_time"],
            "exit_time":t.get("exit_time"),"exit_reason":t.get("exit_reason"),
            "alignment":t.get("alignment",""),"tp_pct":t.get("tp_pct","")}
            for t in acc["closed_trades"][-50:]][::-1],
    }

def build_market_data():
    """Build market + signal snapshot for WS push"""
    with ws_lock:
        cache = {}
        for pair in PAIRS:
            pd = ws_prices.get(pair, {})
            price = pd.get("price")
            if not price:
                cached = ws_market_cache.get(pair, {}) if ws_market_cache else {}
                price = cached.get("price")
                if not price: continue
                pd = {}
            klist = ws_klines_30m.get(pair, [])
            closes = [k["c"] for k in klist] if len(klist) >= BB_PERIOD else []
            bb = compute_bb(closes) if len(closes) >= BB_PERIOD else ws_market_cache.get(pair, {}).get("bb")
            sig = ws_signal.get(pair) or ws_last_signal.get(pair)
            cache[pair] = {
                "price": price,
                "change": round(pd.get("priceChangePercent") or ws_market_cache.get(pair, {}).get("change", 0), 2),
                "high": pd.get("high") or ws_market_cache.get(pair, {}).get("high"),
                "low": pd.get("low") or ws_market_cache.get(pair, {}).get("low"),
                "volume": pd.get("volume") or ws_market_cache.get(pair, {}).get("volume"),
                "bb": bb,
                "trend": ws_trend.get(pair) or "N/A",
                "sma50": round(ws_sma50.get(pair, 0), 2) if ws_sma50.get(pair) else ws_market_cache.get(pair, {}).get("sma50"),
                "signal": sig,
            }
    return cache

def broadcast_all(event_type="update"):
    if not ws_push_clients: return
    try:
        acc = load_account(); acc = reset_daily(acc); acc = process_signals(acc); acc = check_trades(acc); save_account(acc)
        data = {
            "type": event_type,
            **build_account_data(acc),
            "market": build_market_data(),
        }
        msg = json.dumps(data)
        if ws_push_loop:
            coros = []
            for c in ws_push_clients.copy():
                try:
                    coros.append(asyncio.ensure_future(c.send(msg)))
                except Exception:
                    ws_push_clients.discard(c)
            if coros:
                asyncio.run_coroutine_threadsafe(
                    asyncio.gather(*coros, return_exceptions=True), ws_push_loop)
    except Exception as e:
        log(f"Broadcast error: {e}")

# ─── Initial data fetch (seeds WS state) ───

def fetch_json(url, retries=2):
    import urllib.request
    for i in range(retries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
            with urllib.request.urlopen(req, timeout=15) as r:
                return json.loads(r.read())
        except:
            if i < retries - 1: time.sleep(1)
    return None

def seed_initial_data():
    """Fetch initial klines via REST to bootstrap before WS takes over"""
    global ws_klines_30m, ws_klines_1m, ws_klines_1h, ws_prices, ws_trend, ws_sma50
    BINANCE_BASE = "https://fapi.binance.com"

    for pair in PAIRS:
        # 30m
        data = fetch_json(f"{BINANCE_BASE}/fapi/v1/klines?symbol={pair}&interval=30m&limit={BB_PERIOD+20}")
        if data:
            ws_klines_30m[pair] = [{"t":k[0]//1000,"o":float(k[1]),"h":float(k[2]),
                "l":float(k[3]),"c":float(k[4]),"v":float(k[5])} for k in data]
        # 1m
        data = fetch_json(f"{BINANCE_BASE}/fapi/v1/klines?symbol={pair}&interval=1m&limit=60")
        if data:
            ws_klines_1m[pair] = [{"t":k[0]//1000,"o":float(k[1]),"h":float(k[2]),
                "l":float(k[3]),"c":float(k[4]),"v":float(k[5])} for k in data]
        # 1h
        data = fetch_json(f"{BINANCE_BASE}/fapi/v1/klines?symbol={pair}&interval=1h&limit=55")
        if data:
            klist = [{"t":k[0]//1000,"o":float(k[1]),"h":float(k[2]),
                "l":float(k[3]),"c":float(k[4]),"v":float(k[5])} for k in data]
            ws_klines_1h[pair] = klist
            closes = [x["c"] for x in klist]
            if len(closes) >= 50:
                s50 = sma(closes, 50)
                if s50:
                    ws_sma50[pair] = s50
                    ws_trend[pair] = "LONG" if klist[-1]["c"] > s50 else "SHORT"

        # Ticker
        ticker = fetch_json(f"{BINANCE_BASE}/fapi/v1/ticker/24hr?symbol={pair}")
        if ticker:
            ws_prices[pair] = {
                "price": float(ticker["lastPrice"]),
                "change": float(ticker["lastPrice"]),
                "high": float(ticker["highPrice"]),
                "low": float(ticker["lowPrice"]),
                "volume": float(ticker["volume"]),
                "priceChangePercent": float(ticker["priceChangePercent"]),
            }

        # Last candle timestamp
        if ws_klines_30m.get(pair):
            ws_last_30m_ts[pair] = ws_klines_30m[pair][-1]["t"]

    rebuild_market_cache()
    log("Initial data seeded")

# ─── Backtest Engine ───

BT_BALANCE = 1000.0

def fetch_klines(sym, interval, limit=1000, end_time=None):
    url = f"https://fapi.binance.com/fapi/v1/klines?symbol={sym}&interval={interval}&limit={limit}"
    if end_time: url += f"&endTime={end_time}"
    data = fetch_json(url)
    if not data: return None
    return [{"t":k[0]//1000,"o":float(k[1]),"h":float(k[2]),"l":float(k[3]),"c":float(k[4]),"v":float(k[5])} for k in data]

def fetch_all_klines(sym, interval, days):
    all_k = []; end_time = int(time.time() * 1000)
    min_needed = 55 if interval == "1h" else 35 if interval == "30m" else 1
    needed = max(days * 1440 // (30 if interval == "30m" else (60 if interval == "1h" else 1)), min_needed)
    while len(all_k) < needed:
        batch = fetch_klines(sym, interval, 1000, end_time)
        if not batch or len(batch) < 2: break
        all_k = batch + all_k
        end_time = batch[0]["t"] * 1000 - 1
        if len(batch) < 1000: break
    return all_k[-needed:]

def run_backtest(days):
    if days not in (1, 7, 30): days = min(max(days, 1), 365)
    log(f"Running backtest: {days} day(s)")

    k30_all, k1h_all, k1m_all = {}, {}, {}
    for pair in PAIRS:
        k30_all[pair] = fetch_all_klines(pair, "30m", days)
        k1h_all[pair] = fetch_all_klines(pair, "1h", days)
        k1m_all[pair] = fetch_all_klines(pair, "1m", days)
        log(f"  {pair}: {len(k30_all[pair])} 30m, {len(k1m_all[pair])} 1m")

    trend_cache = {}
    for pair in PAIRS:
        kl = k1h_all[pair]; c = [k["c"] for k in kl]
        for i in range(50, len(kl)):
            s50 = sma(c[:i+1], 50)
            if s50: trend_cache.setdefault(pair, {})[kl[i]["t"]] = "LONG" if kl[i]["c"] > s50 else "SHORT"

    bal = BT_BALANCE; peak = BT_BALANCE; mdd = 0
    signal_ids = set(); cc = 0; paused = 0; daypnl = 0; lday = ""
    dpm = {}; trades = []
    active_positions = []  # [{exit_ts, size}] — tracks overlapping margin

    # Collect all signals across pairs sorted by timestamp
    all_signals = []
    for pair in PAIRS:
        k30 = k30_all[pair]; k1m = k1m_all[pair]
        tm = trend_cache.get(pair, {})
        for i in range(BB_PERIOD + 2, len(k30)):
            sig = detect_signal(k30[:i+1])
            if not sig: continue
            direction = sig["dir"]; price = sig["price"]; ts = k30[i]["t"]
            sid = f"{pair}_{direction}_{ts}"
            if sid in signal_ids: continue; signal_ids.add(sid)
            all_signals.append((ts, pair, direction, price, i, tm, k1m))
    all_signals.sort(key=lambda x: x[0])

    signal_ids.clear()
    for ts, pair, direction, price, i, tm, k1m in all_signals:
        sid = f"{pair}_{direction}_{ts}"
        if sid in signal_ids: continue; signal_ids.add(sid)

        day = datetime.fromtimestamp(ts).strftime("%Y-%m-%d")
        if day != lday: daypnl = 0; lday = day
        if ts < paused: continue
        if daypnl <= bal * DAILY_LOSS_LIMIT_PCT / 100: continue

        # Expire positions that have closed before this signal
        active_positions = [p for p in active_positions if p["exit_ts"] > ts]

        tr = None
        for t_ in sorted(tm.keys()):
            if t_ <= ts: tr = tm[t_]
            else: break

        pm = get_pos_mult(direction, tr)
        margin_used = sum(p["size"] for p in active_positions)
        free_balance = max(0, bal - margin_used)
        sz = free_balance * BASE_POSITION_PCT * pm
        if sz <= 0: continue
        if sz < 0.01: continue

        tpp = TP_ALIGNED_PCT if (tr and direction == tr) else TP_PCT
        notional = sz * LEVERAGE
        tp = price * (1 + tpp) if direction == "LONG" else price * (1 - tpp)
        sl = price * (1 - SL_PCT) if direction == "LONG" else price * (1 + SL_PCT)

        result = "EXPIRY"; ep = price; exit_ts = ts + 3600; expiry = ts + 3600
        for k in k1m:
            if k["t"] <= ts: continue
            if k["t"] > expiry: break
            if direction == "LONG":
                if k["h"] >= tp: result,ep,exit_ts = "TP_HIT",tp,k["t"]; break
                if k["l"] <= sl: result,ep,exit_ts = "SL_HIT",sl,k["t"]; break
            else:
                if k["l"] <= tp: result,ep,exit_ts = "TP_HIT",tp,k["t"]; break
                if k["h"] >= sl: result,ep,exit_ts = "SL_HIT",sl,k["t"]; break
        if result == "EXPIRY":
            for k in k1m:
                if k["t"] <= ts: continue
                if k["t"] > expiry: break
                ep = k["c"]; exit_ts = k["t"]

        # Track margin for overlap
        active_positions.append({"exit_ts": exit_ts, "size": sz})

        pp = (1 if direction == "LONG" else -1) * (ep - price) / price
        pnl = notional * pp; bal += pnl; daypnl += pnl
        dpm[day] = dpm.get(day, 0) + pnl

        if pnl > 0: cc = 0
        else:
            cc += 1
            if cc >= 3: paused = ts + PAUSE_DURATION

        align_label = "ALIGNED" if (tr and direction == tr) else "AGAINST" if tr else "NO_TREND"
        trades.append({
            "pair": pair, "direction": direction,
            "entry_price": round(price, 2), "tp_price": round(tp, 2),
            "sl_price": round(sl, 2), "position_size": round(sz, 2),
            "notional": round(notional, 2), "exit_price": round(ep, 2),
            "pnl": round(pnl, 2), "pnl_pct": round(pp * 100, 2),
            "result": "WIN" if pnl > 0 else "LOSS",
            "exit_reason": result, "alignment": align_label,
            "pos_mult": round(pm, 2),
            "entry_time": datetime.fromtimestamp(ts).strftime("%m-%d %H:%M"),
        })
        peak = max(peak, bal); mdd = max(mdd, (peak - bal) / peak * 100)

    wins = [t for t in trades if t["pnl"] > 0]
    losses = [t for t in trades if t["pnl"] <= 0]
    wr = len(wins)/len(trades)*100 if trades else 0
    aw = sum(t["pnl"] for t in wins)/len(wins) if wins else 0
    al = sum(t["pnl"] for t in losses)/len(losses) if losses else 0
    green_days = sum(1 for v in dpm.values() if v > 0)

    align_stats = {}
    for a in ["ALIGNED", "AGAINST", "NO_TREND"]:
        at = [t for t in trades if t["alignment"] == a]
        if at:
            aw_ = len([t for t in at if t["pnl"] > 0])
            align_stats[a] = {"trades":len(at),"wins":aw_,"wr":round(aw_/len(at)*100,1),"net":round(sum(t["pnl"] for t in at),2)}

    pair_stats = {}
    for pair in PAIRS:
        pt = [t for t in trades if t["pair"] == pair]
        if pt:
            pw = len([t for t in pt if t["pnl"] > 0])
            pair_stats[pair] = {"trades":len(pt),"wins":pw,"wr":round(pw/len(pt)*100,1),"net":round(sum(t["pnl"] for t in pt),2)}

    log(f"Backtest complete: ${BT_BALANCE} -> ${round(bal,2)} ({round((bal-BT_BALANCE)/BT_BALANCE*100,1)}%)")
    return {
        "initial_balance": BT_BALANCE, "final_balance": round(bal, 2),
        "return_pct": round((bal - BT_BALANCE) / BT_BALANCE * 100, 1),
        "total_trades": len(trades), "wins": len(wins), "losses": len(losses),
        "win_rate": round(wr, 1), "avg_win": round(aw, 2), "avg_loss": round(al, 2),
        "max_dd": round(mdd, 1), "trading_days": len(dpm),
        "green_days": green_days, "red_days": len(dpm) - green_days,
        "alignment": align_stats, "pairs": pair_stats,
        "leverage": LEVERAGE, "base_position": f"{BASE_POSITION_PCT*100:.0f}%",
        "tp_pct": f"{TP_PCT*100:.1f}%", "sl_pct": f"{SL_PCT*100:.1f}%",
        "trade_log": trades[-500:],
    }

# ─── Main ───

def main():
    log("="*60)
    log(f"  AARIB v3.8 MAX — 125x/40% ULTRA SCALPER")
    log("="*60)
    log(f"  Balance: ${BALANCE_INIT} | Leverage: {LEVERAGE}x | Base: {BASE_POSITION_PCT*100:.0f}%")
    log(f"  TP: {TP_PCT*100:.1f}% / {TP_ALIGNED_PCT*100:.1f}% (aligned) | SL: {SL_PCT*100:.1f}%")
    log(f"  Sizing: against={POS_MULT_AGAINST}x aligned={POS_MULT_ALIGNED}x no_trend={POS_MULT_NO_TREND}x")
    log(f"  Pairs: {', '.join(PAIRS)} | 1m exit | Circuit breakers on")
    log("="*60)

    seed_initial_data()
    rebuild_market_cache()

    acc = load_account(); acc = reset_daily(acc); save_account(acc)
    run_dashboard()
    try:
        threading.Thread(target=start_ws_push, daemon=True).start()
        time.sleep(0.5)
    except Exception as e:
        log(f"WS Push server not available: {e} (REST fallback active)")

    # Start WebSocket thread
    ws_thread = threading.Thread(target=run_websocket, daemon=True)
    ws_thread.start()
    mac_notify("🚀 Aarib v3.6", "Regime-Adaptive Scalper LIVE | 1m exit | $100 paper")

    cycle = 0
    while True:
        try:
            time.sleep(5)  # fast loop — no fetching needed
            cycle += 1

            # Rebuild market cache periodically
            if cycle % 6 == 0:  # every ~30s
                rebuild_market_cache()

            # Log status every ~60s
            if cycle % 12 == 0:
                acc = load_account(); acc = reset_daily(acc)
                acc = process_signals(acc); acc = check_trades(acc); save_account(acc)
                bal = acc["balance"]; ot = len(acc["open_trades"])
                dpnl = acc.get("day_pnl", 0)
                pct = (bal / BALANCE_INIT - 1) * 100
                with ws_lock:
                    has_sig = any(v is not None for v in ws_signal.values())
                    prices = {p: ws_prices.get(p, {}).get("price", 0) for p in PAIRS}
                sig_str = "⚠ SIGNAL" if has_sig else "idle"
                price_str = " | ".join(f"{p[:3]}: ${prices[p]:.2f}" for p in PAIRS)
                paused = acc.get("paused_until", 0)
                pause_str = f" ⏸️{(paused-ts_now())//60:.0f}m" if paused > ts_now() else ""
                log(f"CYCLE {cycle} | Bal: ${bal:.2f} ({pct:+.1f}%) | Day: ${dpnl:+.2f} | "
                    f"Open: {ot} | {acc['wins']}/{acc['total_trades']}W{pause_str} | {sig_str}")
                log(f"  Prices: {price_str}")
            else:
                # Fast cycle — just process signals/trades
                acc = load_account(); acc = reset_daily(acc)
                acc = process_signals(acc); acc = check_trades(acc)
                save_account(acc)
        except KeyboardInterrupt:
            log("Shutdown."); break
        except Exception as e:
            log(f"ERROR: {e}")
            import traceback; traceback.print_exc()
            time.sleep(5)

if __name__ == "__main__":
    main()
