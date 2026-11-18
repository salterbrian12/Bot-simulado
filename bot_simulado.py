# -*- coding: utf-8 -*-
"""
BOT SIMULADO - regla de 4 horas en 6 monedas (BTC, ETH, SOL, BNB, DOGE, ADA)

Que hace:
  - Cada 15 minutos lee precios publicos de Binance Futuros (sin cuenta ni claves).
  - Aplica reglas fijas sobre velas de 4 horas y decide entradas y salidas.
  - NO opera con dinero: anota operaciones ficticias con un capital simulado.
  - Lleva CUATRO cuentas en paralelo, cada una con su propio capital, para comparar
    (las cuatro que mejor resultado dejaron en la prueba historica 2023-2026):
        1. Stop movil 60 dias + entradas cuidadas            (la regla principal desde el 18/11/2026:
                                                               mas ganadoras, menor caida y mejor rendimiento anual)
        2. Stop movil, limite 60 dias                        (la principal anterior)
        3. Stop movil + objetivo movil, limite 60 dias       (deja correr las ganadoras)
        4. Stop movil + objetivo movil, limite 30 dias
  - Guarda todo en la carpeta "bot_simulado" (al lado de este archivo):
        panel.html         -> abrilo con doble clic para ver el estado
        operaciones.csv    -> todas las operaciones de las cuatro reglas (el archivo para analizar)
        datos/             -> velas descargadas
        config.json        -> fecha de inicio y capital

Uso: doble clic. Al abrirlo se pone al dia solo y abre el panel en el navegador.
  python bot_simulado.py            -> queda corriendo y revisa cada 15 minutos
  python bot_simulado.py --una-vez  -> se pone al dia, actualiza el panel y termina
Para que corra solo en segundo plano (sin ventana) cada vez que se prende la PC: instalar_inicio_windows.bat
Lo que va haciendo queda anotado en bot_simulado/registro.txt
NO hace falta dejar la computadora prendida: si estuvo apagada, suspendida o con el bot cerrado,
al volver a abrirlo reconstruye todo lo que paso en el medio (entradas, stops, objetivos) con los
precios reales de ese periodo. No se pierde ninguna operacion.

La cuenta simulada arranca el 1 de septiembre de 2026 para que haya operaciones que mirar desde
el primer dia. Lo que pase desde tu primer encendido se marca como "en vivo": esa es la prueba real.

Las reglas (no cambian solas; cualquier ajuste se decide y se valida aparte):
  - Senal: EMA 9/50/100/200 comprimidas (ancho de la cinta en el 40% mas bajo de los ultimos 90 dias).
      COMPRA: el precio cierra por encima de las EMA 9 y 50 (la vela anterior no lo hacia) con RSI > 52
      VENTA : el precio cierra por debajo de las EMA 9 y 50 (la vela anterior no lo hacia) con RSI < 48
  - Filtro de lateralizacion: no se entra si el mercado viene lateral (rango de 30 dias muy amplio,
    ultimos 5 dias de ida y vuelta, o muchos cruces de la EMA 50).
  - Entrada en la apertura de la vela siguiente. Objetivo 15% y stop 5%, escalados por la
    volatilidad de cada moneda. Salida por tiempo a los 60 dias (30 en la cuenta 4).
  - Varias posiciones: cada senal abre una posicion nueva, salvo que haya posiciones del lado
    contrario abiertas en esa moneda.
  - Stop movil: al cierre de cada vela de 4 h el stop sigue al precio a 1,5 veces el riesgo inicial.
    Nunca retrocede.
  - Riesgo: 1% del capital por posicion.
  - Se actualiza solo: cada 15 minutos busca en GitHub (repositorio Bot-simulado) si hay una version
    nueva de este archivo; si la hay, se reemplaza, guarda la anterior en bot_simulado/bot_simulado_anterior.py
    y se reinicia. No hace falta volver a descargarlo.
  - Cierre a mano: desde el panel web (celular o PC) se puede cerrar una posicion al precio del momento.
    Con la clave de GitHub cargada en el panel, el cierre queda guardado en el repositorio Bot-simulado
    y este bot lo toma solo en el proximo ciclo. Sin clave, pegar el codigo del panel en bot_simulado/cierres_pegados.txt
  - Objetivo movil (cuentas 3 y 4): el objetivo no queda fijo; se mantiene siempre 3 veces el riesgo
    por delante del mejor cierre, asi la posicion sale por stop movil o por tiempo y no corta la ganancia.
  - Entradas cuidadas (solo en la cuenta 1): no entra si el precio ya se alejo mas de 3% de la
    EMA 50 a favor de la senal (ajustado por moneda), y el stop nunca queda a menos de 4,5 ATR:
    con el mercado muy movido el stop se aleja y la posicion se achica, asi el riesgo sigue en 1%.
"""

import csv
import heapq
import json
import os
import shutil
import subprocess
import sys
import time
import urllib.parse
import urllib.error
import urllib.request
import webbrowser
from datetime import datetime, timedelta, timezone

# ------------------------------ CONFIGURACION ------------------------------
CAPITAL_INICIAL = 2000.0
RIESGO_POR_OPERACION = 0.01          # 1% del capital si salta el stop
COMPRESION = 0.40
OBJETIVO = 0.15
STOP = 0.05
MAX_VELAS = 180                      # 30 dias (limite de tiempo por defecto)
MAX_VELAS_PRINCIPAL = 360            # 60 dias para la regla principal
VENTANA_CINTA = 540                  # 90 dias de velas de 4 h
# factor de volatilidad respecto de BTC (medido con datos de 2023)
MONEDAS = {"BTCUSDT": 1.000, "ETHUSDT": 1.140, "SOLUSDT": 2.538, "BNBUSDT": 1.148, "DOGEUSDT": 1.693, "ADAUSDT": 1.846}
COSTO = {"BTCUSDT": 0.0014, "ETHUSDT": 0.0014}   # ida y vuelta; el resto 0,20%
COSTO_OTRAS = 0.0020
ANCLA = "2025-01-01"                 # desde donde se descargan velas (fijo, para que el calculo no cambie)
INICIO_CUENTA = "2026-09-01"         # la cuenta simulada arranca aca (con precios reales), para ver operaciones desde el primer dia.
                                     # Lo operado desde que prendiste el bot por primera vez se cuenta aparte como "en vivo".
# Filtro de lateralizacion (umbrales fijados con datos de 2023-24). No cambia las operaciones:
# solo marca cuales lo pasan, para comparar la regla base contra la regla filtrada.
FILTRO_RANGO_30D = 25.84       # rango maximo de los ultimos 30 dias, en % (escalado por volatilidad)
FILTRO_EFICIENCIA_5D = 0.0966  # avance neto / recorrido total de los ultimos 5 dias, minimo
FILTRO_CRUCES_10D = 7          # cruces de la EMA 50 en los ultimos 10 dias, maximo
STOP_MOVIL_R = 1.5             # distancia del stop movil, en veces el riesgo inicial
# Contra las perdidas rapidas (regla "cuidada"):
MAX_DIST_EMA50 = 3.0           # no entra si el precio ya se alejo mas de 3% (ajustado por moneda) de la EMA 50, a favor de la senal
OBJETIVO_MOVIL_R = 3.0          # objetivo movil: queda siempre 3 R por delante del mejor cierre (solo en las reglas que lo usan)
STOP_MIN_ATR = 4.5             # el stop nunca queda a menos de 4,5 ATR; si se ensancha, la posicion se achica (el riesgo sigue en 1%)
# Las cuentas que se llevan en paralelo. La primera es la principal.
REGLAS = [
    ("cuidada", "Stop movil 60 dias + entradas cuidadas", {"filtro": True, "varias": True, "movil": STOP_MOVIL_R, "max_velas": MAX_VELAS_PRINCIPAL, "max_ema50": MAX_DIST_EMA50, "stop_min_atr": STOP_MIN_ATR}),
    ("movil60", "Stop movil, 60 dias", {"filtro": True, "varias": True, "movil": STOP_MOVIL_R, "max_velas": MAX_VELAS_PRINCIPAL}),
    ("objmovil60", "Stop movil + objetivo movil, 60 dias", {"filtro": True, "varias": True, "movil": STOP_MOVIL_R, "max_velas": MAX_VELAS_PRINCIPAL, "tp_movil": OBJETIVO_MOVIL_R}),
    ("objmovil30", "Stop movil + objetivo movil, 30 dias", {"filtro": True, "varias": True, "movil": STOP_MOVIL_R, "tp_movil": OBJETIVO_MOVIL_R}),
]
CADA_SEG = 900
# ---------------------------------------------------------------------------

BASE = "https://fapi.binance.com"
H4 = 4 * 3600
AR = timezone(timedelta(hours=-3))
CARPETA = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bot_simulado")
DATOS = os.path.join(CARPETA, "datos")


def ahora():
    return int(time.time())


def anotar(linea):
    """Muestra la linea y la guarda en bot_simulado/registro.txt (sirve cuando corre sin ventana)."""
    try:
        print(linea)
    except Exception:
        pass
    try:
        os.makedirs(CARPETA, exist_ok=True)
        ruta = os.path.join(CARPETA, "registro.txt")
        previas = []
        if os.path.exists(ruta):
            with open(ruta, encoding="utf-8") as f:
                previas = f.read().splitlines()[-400:]
        with open(ruta, "w", encoding="utf-8") as f:
            f.write("\n".join(previas + [linea]) + "\n")
    except Exception:
        pass


def fecha(ts):
    return datetime.fromtimestamp(ts, tz=AR).strftime("%d/%m/%Y %H:%M")


def pedir(ruta, params):
    url = BASE + ruta + "?" + urllib.parse.urlencode(params)
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    ultimo = None
    for intento in range(3):
        try:
            with urllib.request.urlopen(req, timeout=25) as resp:
                return json.loads(resp.read().decode("utf-8"))
        except Exception as e:
            ultimo = e
            time.sleep(2 * (intento + 1))
    raise RuntimeError(str(ultimo))


# ------------------------------ DATOS ------------------------------
def leer_cache(simbolo):
    ruta = os.path.join(DATOS, simbolo + "_4h.csv")
    velas = []
    if os.path.exists(ruta):
        with open(ruta, newline="", encoding="utf-8") as f:
            for r in csv.reader(f):
                if r and r[0] != "t":
                    velas.append([int(r[0]), float(r[1]), float(r[2]), float(r[3]), float(r[4])])
    return velas


def guardar_cache(simbolo, velas):
    ruta = os.path.join(DATOS, simbolo + "_4h.csv")
    tmp = ruta + ".tmp"
    with open(tmp, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["t", "open", "high", "low", "close"])
        w.writerows(velas)
    os.replace(tmp, ruta)


def traer_velas(simbolo, desde_ts):
    """Devuelve velas de 4 h [t, o, h, l, c, cerrada] desde desde_ts (incluye la vela en curso)."""
    out, cursor, t_ahora = [], desde_ts * 1000, ahora() * 1000
    while True:
        datos = pedir("/fapi/v1/klines", {"symbol": simbolo, "interval": "4h", "startTime": cursor, "limit": 1500})
        if not datos:
            break
        for v in datos:
            out.append([v[0] // 1000, float(v[1]), float(v[2]), float(v[3]), float(v[4]), v[6] < t_ahora])
        cursor = datos[-1][0] + H4 * 1000
        if len(datos) < 1500:
            break
        time.sleep(0.3)
    return out


def traer_funding(simbolo, t_desde, t_hasta):
    """Suma de tasas de funding con hora en (t_desde, t_hasta]."""
    total, cursor = 0.0, t_desde * 1000 + 1
    while cursor <= t_hasta * 1000:
        datos = pedir("/fapi/v1/fundingRate", {"symbol": simbolo, "startTime": cursor, "endTime": t_hasta * 1000, "limit": 1000})
        if not datos:
            break
        for x in datos:
            total += float(x["fundingRate"])
        cursor = int(datos[-1]["fundingTime"]) + 1
        if len(datos) < 1000:
            break
    return total


def actualizar(simbolo):
    """Actualiza el cache y devuelve (velas cerradas, vela en curso o None, mensaje de error o None)."""
    velas = leer_cache(simbolo)
    ancla = int(datetime.strptime(ANCLA, "%Y-%m-%d").replace(tzinfo=timezone.utc).timestamp())
    desde = velas[-1][0] + H4 if velas else ancla
    en_curso, error = None, None
    try:
        nuevas = traer_velas(simbolo, desde)
        agregadas = [v[:5] for v in nuevas if v[5] and (not velas or v[0] > velas[-1][0])]
        if agregadas:
            velas.extend(agregadas)
            guardar_cache(simbolo, velas)
        abiertas = [v for v in nuevas if not v[5]]
        if abiertas and velas and abiertas[-1][0] == velas[-1][0] + H4:
            en_curso = abiertas[-1][:5]
    except Exception as e:
        error = str(e)
    return velas, en_curso, error


# ------------------------------ INDICADORES ------------------------------
def ema(valores, periodo):
    a, out, e = 2.0 / (periodo + 1), [], None
    for v in valores:
        e = v if e is None else e + a * (v - e)
        out.append(e)
    return out


def rsi14(cierres):
    out, g, p, a = [None], None, None, 1.0 / 14
    for i in range(1, len(cierres)):
        d = cierres[i] - cierres[i - 1]
        gan, per = max(d, 0.0), max(-d, 0.0)
        g = gan if g is None else g + a * (gan - g)
        p = per if p is None else p + a * (per - p)
        out.append(100.0 if p == 0 else 100.0 - 100.0 / (1.0 + g / p))
    return out


def indicadores(velas):
    c = [v[4] for v in velas]
    e9, e50, e100, e200 = ema(c, 9), ema(c, 50), ema(c, 100), ema(c, 200)
    cinta = [(max(e9[i], e50[i], e100[i], e200[i]) - min(e9[i], e50[i], e100[i], e200[i])) / c[i] for i in range(len(c))]
    pct = [None] * len(c)
    for i in range(VENTANA_CINTA - 1, len(c)):
        w = cinta[i - VENTANA_CINTA + 1:i + 1]
        x = cinta[i]
        menores = sum(1 for y in w if y < x)
        iguales = sum(1 for y in w if y == x)
        pct[i] = (menores + (iguales + 1) / 2.0) / VENTANA_CINTA
    return c, e9, e50, pct, rsi14(c)


def extras(velas, k=1.0):
    """Para la regla cuidada: distancia del cierre a la EMA 50 (en %, ajustada por moneda) y ATR de 14 velas como fraccion del precio."""
    c = [v[4] for v in velas]
    e50 = ema(c, 50)
    dist = [(c[i] / e50[i] - 1) * 100 / k for i in range(len(c))]
    atr, a, x = [], 1.0 / 14, None
    for i, v in enumerate(velas):
        tr = v[2] - v[3] if i == 0 else max(v[2] - v[3], abs(v[2] - c[i - 1]), abs(v[3] - c[i - 1]))
        x = tr if x is None else x + a * (tr - x)
        atr.append(x / c[i])
    return dist, atr


def lateral(velas, c, e50, i, k):
    """Mide si el mercado viene lateral en la vela i. Devuelve (pasa el filtro, rango, eficiencia, cruces)."""
    if i < 180:
        return False, None, None, None
    rango = (max(v[2] for v in velas[i - 179:i + 1]) / min(v[3] for v in velas[i - 179:i + 1]) - 1) * 100 / k
    camino = sum(abs(c[j] - c[j - 1]) for j in range(i - 29, i + 1))
    efic = abs(c[i] - c[i - 30]) / camino if camino > 0 else 0.0
    sg = lambda j: int(c[j] > e50[j]) - int(c[j] < e50[j])
    cruces = sum(1 for j in range(i - 59, i + 1) if sg(j) != sg(j - 1))
    return (rango <= FILTRO_RANGO_30D and efic >= FILTRO_EFICIENCIA_5D and cruces <= FILTRO_CRUCES_10D), rango, efic, cruces


def senales(velas, k=1.0):
    """Lista con +1 (compra), -1 (venta) o 0 para cada vela cerrada, mas el estado de la ultima."""
    c, e9, e50, pct, rsi = indicadores(velas)
    s = [0] * len(c)
    filtro = {}
    for i in range(1, len(c)):
        if pct[i] is None or rsi[i] is None or pct[i] >= COMPRESION:
            continue
        arr, arr_prev = c[i] > max(e9[i], e50[i]), c[i - 1] > max(e9[i - 1], e50[i - 1])
        aba, aba_prev = c[i] < min(e9[i], e50[i]), c[i - 1] < min(e9[i - 1], e50[i - 1])
        if arr and not arr_prev and rsi[i] > 52:
            s[i] = 1
        elif aba and not aba_prev and rsi[i] < 48:
            s[i] = -1
        if s[i] != 0:
            filtro[i] = lateral(velas, c, e50, i, k)[0]
    i = len(c) - 1
    estado = None
    if i >= 0 and pct[i] is not None:
        estado = {"precio": c[i], "ema9": e9[i], "ema50": e50[i], "cinta_pct": pct[i], "rsi": rsi[i],
                  "posicion": "arriba" if c[i] > max(e9[i], e50[i]) else "abajo" if c[i] < min(e9[i], e50[i]) else "entre"}
        estado["filtro"], estado["rango"], estado["eficiencia"], estado["cruces"] = lateral(velas, c, e50, i, k)
    return s, estado, filtro


# ------------------------------ SIMULACION ------------------------------
def simular(simbolo, velas, en_curso, inicio_ts, filtro=False, varias=False, movil=None, pre=None, max_velas=None, max_ema50=None, stop_min_atr=None, extra=None, tp_movil=None, manuales=None):
    """Reproduce una regla desde inicio_ts. Devuelve (operaciones, estado de la moneda).
    filtro: descarta las senales con mercado lateral.  varias: permite varias posiciones del mismo lado.
    movil: distancia del stop movil en R (None = stop fijo).  pre: resultado de senales() ya calculado.
    max_ema50: descarta la senal si el precio ya esta mas lejos que eso de la EMA 50, a favor.
    stop_min_atr: ancho minimo del stop en ATR (el objetivo y el stop movil se miden en veces ese stop).
    manuales: cierres a mano {(simbolo, t_entrada): (momento, precio)}; la posicion se cierra a ese precio en ese momento.
    tp_movil: si se indica, el objetivo tambien se mueve: queda siempre a esa cantidad de R por delante del mejor cierre."""
    k = MONEDAS[simbolo]
    tp, st = OBJETIVO * k, STOP * k
    s, estado, fil = pre if pre is not None else senales(velas, k)
    if max_ema50 is not None or stop_min_atr is not None:
        dist50, atr = extra if extra is not None else extras(velas, k)
    barras = velas + ([en_curso] if en_curso else [])      # la vela en curso solo sirve para entrar y para ver stops
    n, ncerr = len(barras), len(velas)
    abiertas, ops = [], []
    for i in range(n):
        cerrada_i = i < ncerr
        sigue = []
        for p in abiertas:
            if i < p["e"]:
                sigue.append(p)
                continue
            sd, ent = p["s"], p["precio_entrada"]
            hi, lo, cl = barras[i][2], barras[i][3], barras[i][4]
            sal = None
            man = manuales.get((simbolo, p["t_entrada"])) if manuales else None
            if man and barras[i][0] + H4 > man[0]:           # cierre a mano: vale desde la vela en la que se pidio
                sal = (man[1], "manual", sd * (man[1] / ent - 1))
            elif (sd == 1 and lo <= p["stop_actual"]) or (sd == -1 and hi >= p["stop_actual"]):
                sal = (p["stop_actual"], "stop movil" if p["movido"] else "stop", sd * (p["stop_actual"] / ent - 1))
            elif (sd == 1 and hi >= p["objetivo"]) or (sd == -1 and lo <= p["objetivo"]):
                sal = (p["objetivo"], "objetivo", sd * (p["objetivo"] / ent - 1))
            elif cerrada_i and i == p["e"] + (max_velas or MAX_VELAS) - 1:
                sal = (cl, "tiempo", sd * (cl / ent - 1))
            if sal:
                p["precio_salida"], p["motivo"], p["bruto"] = sal
                p["estado"], p["t_salida"] = "cerrada", (max(man[0], p["t_entrada"]) if sal[1] == "manual" else barras[i][0])
                ops.append(p)
                continue
            if movil is not None and cerrada_i:              # el stop se mueve solo con velas cerradas y rige desde la siguiente
                p["mejor"] = max(p["mejor"], sd * (cl / ent - 1) / p["riesgo"])
                nuevo = ent * (1 + sd * (p["mejor"] - movil) * p["riesgo"])
                if sd * (nuevo - p["stop_actual"]) > 1e-12:
                    p["stop_actual"], p["movido"] = nuevo, True
                if tp_movil is not None:
                    p["objetivo"] = ent * (1 + sd * (p["mejor"] + tp_movil) * p["riesgo"])
            sigue.append(p)
        abiertas = sigue
        if not cerrada_i or s[i] == 0 or i + 1 >= n or velas[i][0] + H4 < inicio_ts:
            continue
        sd = s[i]
        if filtro and not fil.get(i):
            continue
        if any(p["s"] != sd for p in abiertas) or (abiertas and not varias):
            continue
        if max_ema50 is not None and sd * dist50[i] > max_ema50:
            continue
        rg = st if stop_min_atr is None else max(st, stop_min_atr * atr[i])     # riesgo de esta posicion (distancia al stop)
        ent = barras[i + 1][1]
        abiertas.append({"simbolo": simbolo, "lado": "compra" if sd == 1 else "venta", "s": sd, "e": i + 1, "t_entrada": barras[i + 1][0],
                         "precio_entrada": ent, "riesgo": rg, "stop": ent * (1 - sd * rg), "stop_actual": ent * (1 - sd * rg), "objetivo": ent * (1 + sd * rg * tp / st),
                         "objetivo_inicial": ent * (1 + sd * rg * tp / st), "pasa_filtro": bool(fil.get(i)), "apiladas": len(abiertas) + 1, "movido": False, "mejor": 0.0,
                         "estado": "abierta", "t_salida": None, "precio_salida": None, "motivo": "", "bruto": None})
    for p in abiertas:
        p["precio_actual"] = barras[n - 1][4]
        p["flotante"] = p["s"] * (barras[n - 1][4] / p["precio_entrada"] - 1)
        ops.append(p)
    return ops, estado


def cuenta(ops, funding_cache, usar_red=True):
    """Asigna tamano y resultado en dolares a cada operacion, en orden cronologico."""
    ops = sorted(ops, key=lambda x: (x["t_entrada"], x["simbolo"]))
    cerradas = sorted([o for o in ops if o["estado"] == "cerrada"], key=lambda x: x["t_salida"])
    for op in cerradas:                                      # primero el funding de cada cerrada
        clave = "%s|%d|%d" % (op["simbolo"], op["t_entrada"], op["t_salida"])
        if clave not in funding_cache and usar_red:
            try:
                funding_cache[clave] = traer_funding(op["simbolo"], op["t_entrada"], op["t_salida"])
            except Exception:
                pass
        f = funding_cache.get(clave)
        op["funding"] = f
        s = 1 if op["lado"] == "compra" else -1
        op["neto"] = op["bruto"] - s * (f or 0.0) - COSTO.get(op["simbolo"], COSTO_OTRAS)
    capital, pend = CAPITAL_INICIAL, []
    for op in ops:                                           # el tamano usa el capital realizado al momento de entrar
        while pend and pend[0][0] <= op["t_entrada"]:
            capital += heapq.heappop(pend)[2]
        op["tamano_usd"] = capital * RIESGO_POR_OPERACION / op.get("riesgo", STOP * MONEDAS[op["simbolo"]])
        if op["estado"] == "cerrada":
            op["usd"] = op["tamano_usd"] * op["neto"]
            heapq.heappush(pend, (op["t_salida"], id(op), op["usd"]))
        else:
            op["usd_flotante"] = op["tamano_usd"] * op["flotante"]
    return ops


# ------------------------------ SALIDAS ------------------------------
def n2(x, d=2):
    return "" if x is None else ("%." + str(d) + "f") % x


def precio(x):
    return "" if x is None else ("%.2f" % x if x >= 10 else "%.5f" % x)


def escribir_csv(cuentas):
    ruta = os.path.join(CARPETA, "operaciones.csv")
    u = lambda ts: "" if ts is None else datetime.fromtimestamp(ts, tz=timezone.utc).strftime("%Y-%m-%d %H:%M")
    with open(ruta + ".tmp", "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["regla", "moneda", "lado", "estado", "entrada_utc", "precio_entrada", "stop_inicial", "stop_actual", "objetivo", "tamano_usd",
                    "salida_utc", "precio_salida", "motivo", "resultado_bruto_pct", "funding_pct", "resultado_neto_pct", "resultado_usd",
                    "numero_en_serie", "pasa_filtro_lateral", "etapa"])
        for clave, _, _ in REGLAS:
            for o in cuentas[clave]:
                w.writerow([clave, o["simbolo"], o["lado"], o["estado"], u(o["t_entrada"]), o["precio_entrada"], o["stop"], o["stop_actual"], o["objetivo"], round(o["tamano_usd"], 2),
                            u(o["t_salida"]), o["precio_salida"] if o["precio_salida"] is not None else "", o["motivo"],
                            n2(o["bruto"] * 100 if o["bruto"] is not None else None, 3), n2(o.get("funding") * 100 if o.get("funding") is not None else None, 3),
                            n2(o["neto"] * 100 if o.get("neto") is not None else None, 3), n2(o.get("usd")), o["apiladas"], "si" if o.get("pasa_filtro") else "no", etapa(o)])
    os.replace(ruta + ".tmp", ruta)


def resumen(ops):
    c = [o for o in ops if o["estado"] == "cerrada"]
    a = [o for o in ops if o["estado"] == "abierta"]
    gan = sum(o["usd"] for o in c)
    cap, pico, dd = CAPITAL_INICIAL, CAPITAL_INICIAL, 0.0
    for o in sorted(c, key=lambda x: x["t_salida"]):
        cap += o["usd"]
        pico = max(pico, cap)
        dd = max(dd, 1 - cap / pico)
    return {"cerradas": len(c), "abiertas": len(a), "ganadoras": sum(1 for o in c if o["usd"] > 0), "resultado_usd": gan,
            "capital": CAPITAL_INICIAL + gan, "flotante": sum(o["usd_flotante"] for o in a), "caida_max": dd,
            "media_pct": (sum(o["neto"] for o in c) / len(c) * 100) if c else None,
            "expuesto": sum(o["tamano_usd"] for o in a)}


VIVO_TS = [0]


def etapa(o):
    return "en vivo" if o["t_entrada"] >= VIVO_TS[0] else "historica"


def si_stop(o):
    """Resultado si el precio toca el stop tal como esta ahora: (fraccion, USD). Incluye comisiones, no la financiacion."""
    n = (1 if o["s"] == 1 else -1) * (o["stop_actual"] / o["precio_entrada"] - 1) - COSTO.get(o["simbolo"], COSTO_OTRAS)
    return n, o["tamano_usd"] * n


def fila_op(o):
    cls = "pos" if (o.get("usd", o.get("usd_flotante", 0)) or 0) >= 0 else "neg"
    mon = o["simbolo"].replace("USDT", "")
    if o["estado"] == "abierta":
        stop = precio(o["stop_actual"]) + (" (movido)" if o["movido"] else "")
        sp, su = si_stop(o)
        cs = "pos" if su >= 0 else "neg"
        return "<tr><td>%s</td><td>%s</td><td>%d</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td class='%s'><span class='chip'>%s %s%% (USD %s)</span></td><td>%s</td><td>USD %s</td><td class='%s'>%s%% (USD %s)</td><td>%s</td></tr>" % (
            mon, o["lado"], o["apiladas"], fecha(o["t_entrada"]), precio(o["precio_entrada"]), precio(o["precio_actual"]), stop,
            cs, "ganancia" if su >= 0 else "p&eacute;rdida", n2(sp * 100), n2(su), precio(o["objetivo"]),
            n2(o["tamano_usd"], 0), cls, n2(o["flotante"] * 100), n2(o["usd_flotante"]), etapa(o))
    return "<tr><td>%s</td><td>%s</td><td>%d</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td>USD %s</td><td class='%s'>%s%%</td><td class='%s'>USD %s</td><td>%s</td></tr>" % (
        mon, o["lado"], o["apiladas"], fecha(o["t_entrada"]), precio(o["precio_entrada"]), fecha(o["t_salida"]), precio(o["precio_salida"]), o["motivo"],
        n2(o["tamano_usd"], 0), cls, n2(o["neto"] * 100), cls, n2(o["usd"]), etapa(o))


ENC_AB = "<tr><th>Moneda</th><th>Lado</th><th>N&ordm;</th><th>Entrada</th><th>Precio</th><th>Actual</th><th>Stop</th><th>Si toca el stop</th><th>Objetivo</th><th>Tama&ntilde;o</th><th>Flotante</th><th>Etapa</th></tr>"
ENC_CE = "<tr><th>Moneda</th><th>Lado</th><th>N&ordm;</th><th>Entrada</th><th>Precio</th><th>Salida</th><th>Precio</th><th>Motivo</th><th>Tama&ntilde;o</th><th>Resultado</th><th>USD</th><th>Etapa</th></tr>"


def tabla_ab(ops, vacio):
    ab = sorted([o for o in ops if o["estado"] == "abierta"], key=lambda x: (x["simbolo"], x["t_entrada"]))
    return "<div class='wrap'><table>" + ENC_AB + ("".join(fila_op(o) for o in ab) or "<tr><td colspan='12' class='sub'>%s</td></tr>" % vacio) + "</table></div>"


def tabla_ce(ops):
    ce = sorted([o for o in ops if o["estado"] == "cerrada"], key=lambda x: -x["t_salida"])
    return "<div class='wrap'><table>" + ENC_CE + ("".join(fila_op(o) for o in ce) or "<tr><td colspan='12' class='sub'>Todav&iacute;a no se cerr&oacute; ninguna.</td></tr>") + "</table></div>"


def kpi(nombre, valor, cls="", nota=""):
    return "<div><span>%s</span><b class='%s'>%s</b>%s</div>" % (nombre, cls, valor, ("<small>%s</small>" % nota) if nota else "")


def pn(x):
    return "pos" if x >= 0 else "neg"


def seccion_regla(clave, nombre, ops, vivo_ts, es_principal):
    """Una solapa por regla, con cuatro sub-solapas: resultados, abiertas, cerradas y datos."""
    r = resumen(ops)
    ab = [o for o in ops if o["estado"] == "abierta"]
    ce = sorted([o for o in ops if o["estado"] == "cerrada"], key=lambda o: o["t_salida"])
    viv = [o for o in ops if o["t_entrada"] >= vivo_ts]
    vc = [o for o in viv if o["estado"] == "cerrada"]
    vu = sum(o["usd"] for o in vc)
    sst = sum(si_stop(o)[1] for o in ab)
    hasta = sum(max(0.0, (1 if o["s"] == 1 else -1) * (o["precio_actual"] - o["stop_actual"]) / o["precio_actual"]) * o["tamano_usd"] for o in ab) / max(r["capital"], 1) * 100
    h = ["<section class='regla' id='r-%s'>" % clave]
    h.append("<h2>%s%s</h2>" % (nombre.replace("movil", "m&oacute;vil").replace("dias", "d&iacute;as"), " <span class='tag'>principal</span>" if es_principal else ""))
    h.append("<nav class='sub-tabs'>" + "".join("<button type='button' data-sub='%s'>%s</button>" % (k, t) for k, t in (
        ("res", "Resultados"), ("ab", "Abiertas (%d)" % len(ab)), ("ce", "Cerradas (%d)" % len(ce)), ("dat", "Datos"))) + "</nav>")
    # resultados
    h.append("<div class='sub-panel' data-sub='res'><div class='k'>")
    h.append(kpi("Capital", "USD " + n2(r["capital"]), "", "desde USD %s" % n2(CAPITAL_INICIAL, 0)))
    h.append(kpi("Resultado cerrado", "USD " + n2(r["resultado_usd"]), pn(r["resultado_usd"]), "%s%% sobre el capital inicial" % n2(r["resultado_usd"] / CAPITAL_INICIAL * 100, 1)))
    h.append(kpi("Resultado flotante", "USD " + n2(r["flotante"]), pn(r["flotante"]), "%d posiciones abiertas" % r["abiertas"]))
    h.append(kpi("Si saltan todos los stops", "USD " + n2(sst), pn(sst), ("%d de %d stops ya en ganancia" % (sum(1 for o in ab if si_stop(o)[1] >= 0), len(ab))) if ab else "sin posiciones abiertas"))
    h.append(kpi("Hasta los stops", n2(hasta, 1) + "%", "", "del capital se ceder&iacute;a desde el precio actual"))
    h.append(kpi("Expuesto", n2(r["expuesto"] / max(r["capital"], 1), 1) + "x", "", "USD %s en posiciones" % n2(r["expuesto"], 0)))
    h.append(kpi("Ganadoras", (n2(r["ganadoras"] / r["cerradas"] * 100, 1) + "%") if r["cerradas"] else "-", "", "%d de %d cerradas" % (r["ganadoras"], r["cerradas"])))
    h.append(kpi("Peor ca&iacute;da", n2(r["caida_max"] * 100, 1) + "%", "", "desde un pico de capital"))
    h.append(kpi("En vivo", "%d entradas" % len(viv), "", "%d cerradas, %d ganadoras" % (len(vc), sum(1 for o in vc if o["usd"] > 0))))
    h.append(kpi("Resultado en vivo", "USD " + n2(vu), pn(vu), "solo operaciones cerradas"))
    h.append("</div></div>")
    # abiertas y cerradas
    h.append("<div class='sub-panel' data-sub='ab'>" + tabla_ab(ops, "Ninguna por ahora. Con el filtro activo pasan varios d&iacute;as entre se&ntilde;ales.") + "</div>")
    h.append("<div class='sub-panel' data-sub='ce'>" + tabla_ce(ops) + "</div>")
    # datos
    h.append("<div class='sub-panel' data-sub='dat'>")
    if ce:
        gan = [o for o in ce if o["usd"] > 0]
        per = [o for o in ce if o["usd"] <= 0]
        racha = m = 0
        for o in ce:
            m = m + 1 if o["usd"] <= 0 else 0
            racha = max(racha, m)
        mejor = max(ce, key=lambda o: o["usd"])
        peor = min(ce, key=lambda o: o["usd"])
        dur = sum(o["t_salida"] - o["t_entrada"] for o in ce) / len(ce) / 86400
        h.append("<div class='k'>")
        h.append(kpi("Resultado medio", n2(sum(o["neto"] for o in ce) / len(ce) * 100) + "%", pn(sum(o["neto"] for o in ce)), "por operaci&oacute;n cerrada"))
        h.append(kpi("Ganancia media", ("USD " + n2(sum(o["usd"] for o in gan) / len(gan))) if gan else "-", "pos", ("%s%% por ganadora" % n2(sum(o["neto"] for o in gan) / len(gan) * 100)) if gan else ""))
        h.append(kpi("P&eacute;rdida media", ("USD " + n2(sum(o["usd"] for o in per) / len(per))) if per else "-", "neg", ("%s%% por perdedora" % n2(sum(o["neto"] for o in per) / len(per) * 100)) if per else ""))
        h.append(kpi("Mejor operaci&oacute;n", "USD " + n2(mejor["usd"]), "pos", "%s %s, %s" % (mejor["simbolo"].replace("USDT", ""), mejor["lado"], fecha(mejor["t_entrada"])[:10])))
        h.append(kpi("Peor operaci&oacute;n", "USD " + n2(peor["usd"]), pn(peor["usd"]), "%s %s, %s" % (peor["simbolo"].replace("USDT", ""), peor["lado"], fecha(peor["t_entrada"])[:10])))
        h.append(kpi("Duraci&oacute;n media", n2(dur, 1) + " d&iacute;as", "", "de la entrada al cierre"))
        h.append(kpi("Peor racha", "%d seguidas" % racha, "", "operaciones perdedoras"))
        h.append("</div>")
        h.append("<div class='dos'><div><h3>Por motivo de cierre</h3><div class='wrap'><table><tr><th>Motivo</th><th>Operaciones</th><th>Ganadoras</th><th>Resultado</th></tr>")
        for mot in sorted({o["motivo"] for o in ce}):
            g = [o for o in ce if o["motivo"] == mot]
            u = sum(o["usd"] for o in g)
            h.append("<tr><td>%s</td><td>%d</td><td>%d</td><td class='%s'>USD %s</td></tr>" % (mot.replace("movil", "m&oacute;vil"), len(g), sum(1 for o in g if o["usd"] > 0), pn(u), n2(u)))
        h.append("</table></div></div><div><h3>Por lado</h3><div class='wrap'><table><tr><th>Lado</th><th>Operaciones</th><th>Ganadoras</th><th>Resultado</th></tr>")
        for lado in ("compra", "venta"):
            g = [o for o in ce if o["lado"] == lado]
            u = sum(o["usd"] for o in g)
            h.append("<tr><td>%ss</td><td>%d</td><td>%d</td><td class='%s'>USD %s</td></tr>" % (lado, len(g), sum(1 for o in g if o["usd"] > 0), pn(u), n2(u)))
        h.append("</table></div></div></div>")
    else:
        h.append("<div class='sub'>Todav&iacute;a no hay operaciones cerradas.</div>")
    h.append("<h3>Por moneda</h3><div class='wrap'><table><tr><th>Moneda</th><th>Cerradas</th><th>Ganadoras</th><th>Compras</th><th>Ventas</th><th>Resultado medio</th><th>Resultado</th><th>Abiertas ahora</th></tr>")
    for sim in MONEDAS:
        cs = [o for o in ce if o["simbolo"] == sim]
        us = sum(o["usd"] for o in cs)
        ab_s = [o for o in ab if o["simbolo"] == sim]
        h.append("<tr><td>%s</td><td>%d</td><td>%d</td><td>%d</td><td>%d</td><td>%s</td><td class='%s'>USD %s</td><td>%s</td></tr>" % (
            sim.replace("USDT", ""), len(cs), sum(1 for o in cs if o["usd"] > 0), sum(1 for o in cs if o["lado"] == "compra"), sum(1 for o in cs if o["lado"] == "venta"),
            (n2(sum(o["neto"] for o in cs) / len(cs) * 100) + "%") if cs else "-", pn(us), n2(us),
            ("%d %s" % (len(ab_s), ab_s[0]["lado"] + ("s" if len(ab_s) > 1 else ""))) if ab_s else "no"))
    h.append("</table></div></div></section>")
    return "".join(h)


SCRIPT_SOLAPAS = """<script>(function(){
var sel={r:null,s:{}};function g(k){try{return localStorage.getItem(k)}catch(e){return null}}function p(k,v){try{localStorage.setItem(k,v)}catch(e){}}
try{sel=JSON.parse(g('solapas')||'null')||sel}catch(e){}
var h=location.hash.replace('#','').split('-');if(h[0])sel.r=h[0];if(h[1])sel.s[h[0]]=h[1];
var tabs=document.querySelectorAll('.tabs button'),secs=document.querySelectorAll('section.regla, section.extra');
function ver(r){if(!document.getElementById('r-'+r))r=tabs[0].getAttribute('data-r');sel.r=r;
 tabs.forEach(function(b){b.setAttribute('aria-selected',b.getAttribute('data-r')===r)});
 secs.forEach(function(s){s.hidden=s.id!=='r-'+r});var s=document.getElementById('r-'+r);
 var sb=s.querySelectorAll('.sub-tabs button');if(sb.length){var k=sel.s[r]||'res';if(!s.querySelector('.sub-panel[data-sub=\"'+k+'\"]'))k='res';
  sb.forEach(function(b){b.setAttribute('aria-selected',b.getAttribute('data-sub')===k)});
  s.querySelectorAll('.sub-panel').forEach(function(x){x.hidden=x.getAttribute('data-sub')!==k});sel.s[r]=k}
 p('solapas',JSON.stringify(sel));try{history.replaceState(null,'','#'+r+(sel.s[r]?'-'+sel.s[r]:''))}catch(e){}}
tabs.forEach(function(b){b.addEventListener('click',function(){ver(b.getAttribute('data-r'))})});
document.querySelectorAll('.sub-tabs button').forEach(function(b){b.addEventListener('click',function(){sel.s[sel.r]=b.getAttribute('data-sub');ver(sel.r)})});
ver(sel.r||tabs[0].getAttribute('data-r'));})();</script>"""


def escribir_panel(cuentas, vivo_ts, estados, inicio_ts, errores):
    principal = REGLAS[0][0]
    h = []
    h.append("<!doctype html><html lang='es'><head><meta charset='utf-8'><meta http-equiv='refresh' content='300'><title>Bot simulado</title><style>"
             "body{font-family:Segoe UI,Arial,sans-serif;background:#12161d;color:#e4e8ee;margin:0;padding:20px 24px 40px;font-size:14px}h1{font-size:20px;margin:0 0 4px}h2{font-size:17px;margin:18px 0 10px}h3{font-size:13px;margin:18px 0 6px;color:#8e99a8;font-weight:600}"
             ".sub{color:#8e99a8}.k{display:grid;grid-template-columns:repeat(auto-fill,minmax(190px,1fr));gap:10px;margin:12px 0}.k div{background:#1a1f28;border:1px solid #2b323d;border-radius:8px;padding:10px 14px}"
             ".k b{display:block;font-size:19px;font-weight:600;font-variant-numeric:tabular-nums}.k span{color:#8e99a8;font-size:11px;text-transform:uppercase;letter-spacing:.05em}.k small{display:block;color:#8e99a8;font-size:12px;margin-top:2px}"
             "table{border-collapse:collapse;width:100%}th{text-align:left;color:#8e99a8;font-size:11px;text-transform:uppercase;letter-spacing:.05em;font-weight:500;padding:6px 10px}"
             "td{padding:6px 10px;border-top:1px solid #222832;white-space:nowrap;font-variant-numeric:tabular-nums}.pos{color:#5fd66c}.neg{color:#e06c68}.wrap{overflow-x:auto;background:#1a1f28;border:1px solid #2b323d;border-radius:8px}"
             ".av{background:#3a2a12;border:1px solid #6b4a12;border-radius:8px;padding:8px 12px;margin:12px 0}tr.pri td{background:#1f2633}.chip{border-radius:6px;padding:2px 8px;font-weight:600}td.pos .chip{background:#1d3a24}td.neg .chip{background:#40201f}"
             ".tabs{display:flex;gap:6px;flex-wrap:wrap;margin:18px 0 0;border-bottom:1px solid #2b323d;position:sticky;top:0;background:#12161d;padding-top:8px;z-index:2}"
             ".tabs button{font:inherit;color:#c9d1dc;background:#1a1f28;border:1px solid #2b323d;border-bottom:none;border-radius:8px 8px 0 0;padding:8px 14px;cursor:pointer;text-align:left;line-height:1.3}"
             ".tabs button small{display:block;font-size:12px;color:#8e99a8}.tabs button[aria-selected=true]{background:#24406f;border-color:#3d6bb8;color:#fff}.tabs button[aria-selected=true] small{color:#cfe0ff}"
             ".sub-tabs{display:flex;gap:6px;flex-wrap:wrap;margin-bottom:6px}.sub-tabs button{font:inherit;color:#c9d1dc;background:#1a1f28;border:1px solid #2b323d;border-radius:999px;padding:6px 14px;cursor:pointer}"
             ".sub-tabs button[aria-selected=true]{background:#e4e8ee;color:#12161d;border-color:#e4e8ee;font-weight:600}button:focus-visible{outline:2px solid #6ea0ff;outline-offset:2px}"
             ".tag{font-size:11px;background:#24406f;color:#cfe0ff;border-radius:999px;padding:2px 8px;vertical-align:middle;margin-left:6px}.dos{display:grid;grid-template-columns:repeat(auto-fit,minmax(320px,1fr));gap:12px}[hidden]{display:none!important}</style></head><body>")
    h.append("<h1>Bot simulado &middot; regla de 4 horas</h1><div class='sub'>Operaciones ficticias con precios reales, sin dinero. Cuenta simulada desde %s &middot; prueba en vivo desde %s &middot; actualizado %s (hora de Buenos Aires) &middot; versi&oacute;n %s</div>" % (fecha(inicio_ts), fecha(vivo_ts), fecha(ahora()), VERSION))
    h.append("<div class='sub' style='margin-top:4px'>Cierres a mano: %d en total entre las cuatro cuentas%s. Las operaciones &laquo;hist&oacute;rica&raquo; entraron antes de tu primer encendido; las &laquo;en vivo&raquo; son la prueba real.</div>" % (SYNC["n"], {True: " &middot; sincronizados con el panel del celular", False: " &middot; <span class='neg'>no pude leer GitHub, uso la &uacute;ltima copia guardada</span>", None: ""}[SYNC["ok"]]))
    if errores:
        h.append("<div class='av'>Sin conexi&oacute;n para: %s. Se muestran los &uacute;ltimos datos guardados.</div>" % ", ".join(errores))
    # solapas: una por regla, mas la comparacion y el estado de las monedas
    h.append("<nav class='tabs'>")
    for n, (clave, nombre, _) in enumerate(REGLAS, 1):
        x = resumen(cuentas[clave])
        pc = (x["capital"] / CAPITAL_INICIAL - 1) * 100
        h.append("<button type='button' data-r='%s'>%d. %s<small>USD %s &middot; <span class='%s'>%s%%</span> &middot; %d abiertas</small></button>" % (
            clave, n, nombre.replace("movil", "m&oacute;vil").replace("dias", "d&iacute;as"), n2(x["capital"], 0), pn(pc), ("+" if pc >= 0 else "") + n2(pc, 1), x["abiertas"]))
    h.append("<button type='button' data-r='comparar'>Comparar<small>las cuatro, lado a lado</small></button><button type='button' data-r='monedas'>Monedas<small>estado de cada una</small></button></nav>")
    for clave, nombre, _ in REGLAS:
        h.append(seccion_regla(clave, nombre, cuentas[clave], vivo_ts, clave == principal))
    # comparacion
    h.append("<section class='extra' id='r-comparar'><h2>Las reglas, lado a lado</h2><div class='sub'>Cada una tiene su propia cuenta de USD %s y arriesga %s%% por posici&oacute;n.</div><div class='wrap' style='margin-top:8px'><table>"
             "<tr><th>Regla</th><th>Capital</th><th>Resultado cerrado</th><th>Cerradas</th><th>Ganadoras</th><th>Resultado medio</th><th>Peor ca&iacute;da</th><th>Abiertas</th><th>Flotante</th><th>Expuesto</th><th>En vivo: entradas</th><th>En vivo: cerradas</th><th>En vivo: resultado</th></tr>" % (n2(CAPITAL_INICIAL, 0), n2(RIESGO_POR_OPERACION * 100, 1)))
    for clave, nombre, _ in REGLAS:
        x = resumen(cuentas[clave])
        viv = [o for o in cuentas[clave] if o["t_entrada"] >= vivo_ts]
        vc = [o for o in viv if o["estado"] == "cerrada"]
        vu = sum(o["usd"] for o in vc)
        h.append("<tr%s><td>%s</td><td>USD %s</td><td class='%s'>USD %s</td><td>%d</td><td>%s</td><td>%s</td><td>%s%%</td><td>%d</td><td class='%s'>USD %s</td><td>%sx</td><td>%d</td><td>%s</td><td class='%s'>USD %s</td></tr>" % (
            " class='pri'" if clave == principal else "", nombre.replace("movil", "m&oacute;vil"), n2(x["capital"]), pn(x["resultado_usd"]), n2(x["resultado_usd"]), x["cerradas"],
            ("%d de %d" % (x["ganadoras"], x["cerradas"])) if x["cerradas"] else "-", (n2(x["media_pct"]) + "%") if x["cerradas"] else "-", n2(x["caida_max"] * 100, 1),
            x["abiertas"], pn(x["flotante"]), n2(x["flotante"]), n2(x["expuesto"] / max(x["capital"], 1), 1),
            len(viv), ("%d (%d ganadoras)" % (len(vc), sum(1 for o in vc if o["usd"] > 0))) if vc else "0", pn(vu), n2(vu)))
    h.append("</table></div></section>")
    # monedas
    h.append("<section class='extra' id='r-monedas'><h2>Estado de cada moneda</h2><div class='wrap'><table><tr><th>Moneda</th><th>Precio</th><th>Contra EMA 9 y 50</th><th>RSI</th><th>Compresi&oacute;n de EMAs</th><th>Mercado lateral</th><th>Lectura</th></tr>")
    for sim in MONEDAS:
        e = estados.get(sim)
        if not e:
            h.append("<tr><td>%s</td><td colspan='6' class='sub'>sin datos suficientes</td></tr>" % sim.replace("USDT", ""))
            continue
        comp = e["cinta_pct"] < COMPRESION
        if e.get("rango") is None:
            lat, lect = "sin datos", ""
        else:
            lat = ("no" if e["filtro"] else "s&iacute;") + " (rango %s%%, eficiencia %s, %d cruces)" % (n2(e["rango"], 0), n2(e["eficiencia"]), e["cruces"])
            lect = ("Lista: una ruptura de las EMA con RSI a favor abre posici&oacute;n" if e["filtro"] else "Comprimida pero lateral: la se&ntilde;al se descartar&iacute;a") if comp else "EMAs abiertas: no hay se&ntilde;al hasta que se compriman"
        h.append("<tr><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td>%s (percentil %d)</td><td>%s</td><td class='sub'>%s</td></tr>" % (
            sim.replace("USDT", ""), precio(e["precio"]), e["posicion"], n2(e["rsi"], 0), "s&iacute;" if comp else "no", round(e["cinta_pct"] * 100), lat, lect))
    h.append("</table></div></section>")
    h.append(SCRIPT_SOLAPAS + "</body></html>")
    ruta = os.path.join(CARPETA, "panel.html")
    with open(ruta + ".tmp", "w", encoding="utf-8") as f:
        f.write("".join(h))
    os.replace(ruta + ".tmp", ruta)


# ------------------------------ CICLO ------------------------------
VERSION = "2026-11-18b"            # cambia con cada version nueva; se muestra en el panel
CODIGO_GITHUB = "https://raw.githubusercontent.com/salterbrian12/Bot-simulado/main/bot_simulado.py"


def autoactualizar():
    """Busca en GitHub la ultima version de este archivo. Si hay una distinta y es un programa valido,
    guarda una copia de la actual en bot_simulado/bot_simulado_anterior.py, se reemplaza y devuelve True.
    Si no hay conexion o algo falla, sigue con la version actual."""
    yo = os.path.abspath(__file__)
    try:
        req = urllib.request.Request(CODIGO_GITHUB + "?t=%d" % int(time.time()), headers={"User-Agent": "bot-simulado", "Cache-Control": "no-cache"})
        with urllib.request.urlopen(req, timeout=20) as resp:
            nuevo = resp.read()
        with open(yo, "rb") as f:
            actual = f.read()
    except Exception:
        return False
    if nuevo.replace(b"\r\n", b"\n") == actual.replace(b"\r\n", b"\n") or b"def autoactualizar" not in nuevo or b"BOT SIMULADO" not in nuevo:
        return False
    try:
        compile(nuevo, "bot_simulado.py", "exec")
    except SyntaxError as e:
        anotar("%s | la version nueva de GitHub tiene un error, sigo con la actual: %s" % (fecha(ahora()), e))
        return False
    try:
        os.makedirs(CARPETA, exist_ok=True)
        shutil.copyfile(yo, os.path.join(CARPETA, "bot_simulado_anterior.py"))
        with open(yo + ".nuevo", "wb") as f:
            f.write(nuevo)
        os.replace(yo + ".nuevo", yo)
    except Exception as e:
        anotar("%s | no pude instalar la version nueva, sigo con la actual: %s" % (fecha(ahora()), e))
        return False
    anotar("%s | se instalo una version nueva del bot desde GitHub; la anterior quedo en bot_simulado_anterior.py. Reiniciando." % fecha(ahora()))
    return True


def reiniciar():
    """Arranca de nuevo este mismo archivo (ya actualizado) y cierra el proceso actual."""
    try:
        subprocess.Popen([sys.executable, os.path.abspath(__file__)] + sys.argv[1:], cwd=os.path.dirname(os.path.abspath(__file__)))
    except Exception as e:
        anotar("%s | no pude reiniciar solo; la version nueva se usa la proxima vez que abras el bot: %s" % (fecha(ahora()), e))
        return
    os._exit(0)


CIERRES_GITHUB = "https://raw.githubusercontent.com/salterbrian12/Bot-simulado/main/cierres.txt"
SYNC = {"ok": None, "n": 0}      # estado de la ultima lectura de GitHub, para mostrarlo en el panel


def leer_manuales():
    """Junta los cierres a mano de dos lugares:
      - GitHub: los que hiciste desde el panel web (celular o navegador) con la clave cargada; se leen solos en cada ciclo.
        La ultima copia se guarda en cierres_github_v2.txt para cuando no hay conexion.
      - bot_simulado/cierres_pegados.txt: el codigo copiado del panel web, pegado a mano (si no usas la clave).
    Formato de cada linea: regla|moneda|entrada|momento|precio. Si un cierre aparece en los dos, vale el primero."""
    out = {clave: {} for clave, _, _ in REGLAS}
    textos = []
    copia = os.path.join(CARPETA, "cierres_github_v2.txt")
    try:
        req = urllib.request.Request(CIERRES_GITHUB + "?t=%d" % int(time.time()), headers={"User-Agent": "bot-simulado", "Cache-Control": "no-cache"})
        with urllib.request.urlopen(req, timeout=15) as resp:
            t = resp.read().decode("utf-8", "replace")
        with open(copia + ".tmp", "w", encoding="utf-8") as f:
            f.write(t)
        os.replace(copia + ".tmp", copia)
        SYNC["ok"] = True
        textos.append(t)
    except urllib.error.HTTPError as e:
        SYNC["ok"] = True if e.code == 404 else False      # 404: todavia no se hizo ningun cierre desde el panel
    except Exception:
        SYNC["ok"] = False
    if SYNC["ok"] is False:
        try:
            with open(copia, encoding="utf-8") as f:
                textos.append(f.read())
        except Exception:
            pass
    try:
        with open(os.path.join(CARPETA, "cierres_pegados.txt"), encoding="utf-8") as f:
            textos.append(f.read())
    except Exception:
        pass
    for texto in textos:
        for parte in texto.replace("\n", ";").split(";"):
            x = parte.strip().split("|")
            try:
                if len(x) == 5 and x[0] in out and x[1] in MONEDAS and float(x[4]) > 0 and (x[1], int(x[2])) not in out[x[0]]:
                    out[x[0]][(x[1], int(x[2]))] = (int(x[3]), float(x[4]))
            except ValueError:
                pass
    SYNC["n"] = sum(len(v) for v in out.values())
    return out


def cargar_json(nombre, defecto):
    try:
        with open(os.path.join(CARPETA, nombre), encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return defecto


def guardar_json(nombre, obj):
    ruta = os.path.join(CARPETA, nombre)
    with open(ruta + ".tmp", "w", encoding="utf-8") as f:
        json.dump(obj, f, indent=1)
    os.replace(ruta + ".tmp", ruta)


def ciclo(avisar=True):
    os.makedirs(DATOS, exist_ok=True)
    cfg = cargar_json("config.json", None)
    if cfg is None:
        cfg = {"inicio": ahora(), "capital_inicial": CAPITAL_INICIAL}
        guardar_json("config.json", cfg)
    vivo = int(cfg["inicio"])                                # primer encendido: desde aca es prueba en vivo
    inicio = min(vivo, int(datetime.strptime(INICIO_CUENTA, "%Y-%m-%d").replace(tzinfo=timezone.utc).timestamp()))
    VIVO_TS[0] = vivo
    fcache = cargar_json("funding.json", {})
    vistos = cargar_json("vistos_%s.json" % REGLAS[0][0], None)
    cuentas = {clave: [] for clave, _, _ in REGLAS}
    manuales = leer_manuales()
    estados, errores = {}, []
    for sim in MONEDAS:
        velas, en_curso, err = actualizar(sim)
        if err:
            errores.append(sim.replace("USDT", ""))
        if len(velas) < VENTANA_CINTA + 5:
            continue
        pre = senales(velas, MONEDAS[sim])
        extra = extras(velas, MONEDAS[sim])
        estados[sim] = pre[1]
        for clave, _, kw in REGLAS:
            cuentas[clave].extend(simular(sim, velas, en_curso, inicio, pre=pre, extra=extra, manuales=manuales[clave], **kw)[0])
    for clave in cuentas:
        cuentas[clave] = cuenta(cuentas[clave], fcache, not errores)
    guardar_json("funding.json", fcache)
    escribir_csv(cuentas)
    escribir_panel(cuentas, vivo, estados, inicio, errores)
    # avisos de novedades (solo de la regla principal)
    ops = cuentas[REGLAS[0][0]]
    claves = {"%s|%d|%d|%s" % (o["simbolo"], o["t_entrada"], o["apiladas"], o["estado"]): o for o in ops}
    if avisar and vistos is not None:
        for kx, o in claves.items():
            if kx not in vistos:
                if o["estado"] == "abierta":
                    anotar("  >>> NUEVA ENTRADA (%s): %s %s a %s | stop %s | objetivo %s | tamano USD %.0f | posicion numero %d en esa moneda" % (
                        fecha(o["t_entrada"]), o["lado"].upper(), o["simbolo"], precio(o["precio_entrada"]), precio(o["stop"]), precio(o["objetivo"]), o["tamano_usd"], o["apiladas"]))
                else:
                    anotar("  >>> CIERRE (%s): %s %s por %s | resultado %+.2f%% (USD %+.2f)" % (fecha(o["t_salida"]), o["lado"].upper(), o["simbolo"], o["motivo"], o["neto"] * 100, o["usd"]))
    guardar_json("vistos_%s.json" % REGLAS[0][0], sorted(claves))
    return cuentas, estados, errores


def main():
    una_vez = "--una-vez" in sys.argv
    con_ventana = sys.stdout is not None and hasattr(sys.stdout, "isatty") and sys.stdout.isatty()
    if con_ventana:
        print("BOT SIMULADO - regla de 4 horas, cuatro cuentas en paralelo. No opera con dinero real.")
        print("Carpeta de trabajo:", CARPETA)
        print("La primera vez descarga historial y puede tardar un minuto.\n")
    primera = True
    while True:
        if not una_vez and autoactualizar():
            if con_ventana:
                print("Hay una version nueva del bot: se instalo sola y se reinicia.\n")
            reiniciar()
        try:
            cuentas, estados, errores = ciclo(avisar=True)
            r = resumen(cuentas[REGLAS[0][0]])
            if primera:
                viv = [o for o in cuentas[REGLAS[0][0]] if o["t_entrada"] >= VIVO_TS[0]]
                anotar("%s | puesta al dia completa. Regla principal: %d posiciones abiertas, %d cerradas (%d entradas en vivo)." % (fecha(ahora()), r["abiertas"], r["cerradas"], len(viv)))
                if con_ventana and not una_vez:
                    print("Abriendo el panel en el navegador...\n")
                    try:
                        webbrowser.open("file:///" + os.path.join(CARPETA, "panel.html").replace(os.sep, "/").lstrip("/"))
                    except Exception:
                        pass
            listas = [x.replace("USDT", "") for x, e in estados.items() if e and e["cinta_pct"] < COMPRESION and e.get("filtro")]
            anotar("%s | regla principal: capital USD %.2f | abiertas %d | cerradas %d | listas para senal: %s%s" % (
                fecha(ahora()), r["capital"], r["abiertas"], r["cerradas"], ", ".join(listas) if listas else "ninguna",
                (" | SIN CONEXION: " + ", ".join(errores)) if errores else ""))
        except Exception as e:
            anotar("%s | error en este ciclo, reintento en el proximo: %s" % (fecha(ahora()), e))
        primera = False
        if una_vez:
            return
        time.sleep(CADA_SEG)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nFrenado.")
    except Exception as e:
        print("\nERROR:", e)
        try:
            input("Presiona Enter para cerrar...")
        except EOFError:
            pass
        sys.exit(1)
