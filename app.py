from dotenv import dotenv_values
import os as _os
_env = dotenv_values(_os.path.join(_os.path.dirname(__file__), '.env'))
for _k, _v in _env.items():
    _os.environ[_k] = _v

from flask import Flask, render_template, request, jsonify, make_response
import ezdxf
import math
import os
import tempfile
import traceback
import base64
import json
import anthropic
from PIL import Image
import fitz  # PyMuPDF — nepotrebuje poppler
from io import BytesIO
from reportlab.lib.pagesizes import A4
from reportlab.lib import colors
from reportlab.lib.units import mm
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, HRFlowable, Image as RLImage
from reportlab.lib.enums import TA_LEFT, TA_RIGHT, TA_CENTER
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont

# Registruj DejaVu fonty s Unicode podporou (slovenské znaky)
_FONT_DIR = os.path.join(os.path.dirname(__file__), 'fonts')
try:
    from reportlab.pdfbase.cidfonts import UnicodeCIDFont
    from reportlab.lib.fonts import addMapping
    pdfmetrics.registerFont(TTFont('DejaVu',     os.path.join(_FONT_DIR, 'DejaVuSans.ttf')))
    pdfmetrics.registerFont(TTFont('DejaVu-Bold',os.path.join(_FONT_DIR, 'DejaVuSans-Bold.ttf')))
    addMapping('DejaVu', 0, 0, 'DejaVu')
    addMapping('DejaVu', 1, 0, 'DejaVu-Bold')
    _PDF_FONT      = 'DejaVu'
    _PDF_FONT_BOLD = 'DejaVu-Bold'
except Exception:
    _PDF_FONT      = 'Helvetica'
    _PDF_FONT_BOLD = 'Helvetica-Bold'

app = Flask(__name__)
app.config['MAX_CONTENT_LENGTH'] = 50 * 1024 * 1024  # 50MB max (TIF súbory)

# ─────────────────────────────────────────────
#  REZNÉ RÝCHLOSTI (m/min) — GRYF 4022P 12kW
#  Zdroj: oficiálne 12kW kalkulačné dáta (HGLASER)
#  Hodnoty = stred rozsahu, interpolácia pre medzičlánky
#  ocel 1-3mm: N2/vzduch, 5mm+: O2
#  nerez: N2, hlinik: N2
# ─────────────────────────────────────────────
CUTTING_SPEEDS = {
    "ocel": {
        1: 37.5, 3: 17.0, 5: 5.0, 10: 2.6, 15: 1.75, 20: 1.2, 25: 0.875
    },
    "nerez": {
        1: 50.0, 3: 20.0, 5: 10.0, 10: 3.85, 15: 2.0, 20: 1.25
    },
    "hlinik": {
        2: 30.0, 5: 13.0, 10: 5.0, 20: 1.35
    },
    "pozink": {  # DX51D+Z — podobné oceľi, ~10% pomalšie (Zn povlak)
        1: 34.0, 3: 15.0, 5: 4.5, 10: 2.3, 15: 1.6, 20: 1.1
    },
}

# ─────────────────────────────────────────────
#  ČASY PREPALU (s) podľa materiálu a hrúbky
#  Zdroj: HGLASER 12kW oficiálne dáta
#  FlyCut = takmer nulový čas pre tenké mat.
# ─────────────────────────────────────────────
PIERCE_TIME = {
    "ocel":  {1: 0.02, 3: 0.05, 5: 0.15, 10: 0.30, 15: 0.50, 20: 0.80, 25: 1.20},
    "nerez": {1: 0.01, 3: 0.03, 5: 0.10, 10: 0.25, 15: 0.45, 20: 0.70},
    "hlinik":{2: 0.02, 5: 0.08, 10: 0.20, 20: 0.60},
    "pozink":{1: 0.02, 3: 0.05, 5: 0.15, 10: 0.30, 15: 0.50, 20: 0.80},
}

# ─────────────────────────────────────────────
#  REZNÝ PLYN — výber podľa materiálu a hrúbky
#  + náklady na plyn (€/s rezania)
# ─────────────────────────────────────────────
def select_gas(material: str, thickness_mm: float) -> dict:
    """Vyberie optimálny rezný plyn a vráti jeho náklady €/s."""
    GAS_COST = {
        "vzduch": 0.0008,  # kompresor — takmer zadarmo
        "N2":     0.0045,  # dusík — vysokotlak, spotrebný
        "O2":     0.0025,  # kyslík — lacnejší ako N2
    }
    if material == "ocel":
        gas = "vzduch" if thickness_mm <= 3 else ("N2" if thickness_mm <= 5 else "O2")
    elif material == "nerez":
        gas = "vzduch" if thickness_mm <= 3 else "N2"
    elif material == "hlinik":
        gas = "N2"
    elif material == "pozink":
        gas = "vzduch" if thickness_mm <= 3 else "N2"
    else:
        gas = "N2"
    return {"gas": gas, "cost_per_sec": GAS_COST[gas]}


# ─────────────────────────────────────────────
#  PARAMETRE STROJA — GRYF 4022P KOMBI 12kW
#  Zdroj: HGLASER CZ dokumentácia
# ─────────────────────────────────────────────
MACHINE_PARAMS = {
    "rapid_traverse_m_min": 140,  # rýchlozlom m/min (HGLASER CZ, str.7)
    "acceleration_g": 1.0,        # max zrýchlenie (HGLASER CZ, str.7)
    "frog_jump_sec": 1.0,         # Frog Jump: čas na vnútornú kontúru (zdvih+presun+spust)
    "cutting_safety_factor": 1.35,# korekcia na akceleráciu/rohy/optiku (×1.35)
    "min_machine_time_min": 0.25, # min strojový čas/ks (15s)
    "table_exchange_sec": 40,     # výmena palety pri full tabuli (s)
}

# Cena materiálu €/kg (orientačné, upraviteľné)
MATERIAL_PRICE_PER_KG = {
    "ocel":  1.05,  # S235/S355 čierny plech, nákup bez DPH (0.95–1.15 €/kg)
    "nerez": 3.40,  # AISI 304 / 1.4301, nákup bez DPH (3.20–3.60 €/kg)
    "hlinik": 4.90, # AlMg3 / Al99.5, nákup bez DPH (4.70–5.10 €/kg)
    "pozink": 1.30, # DX51D+Z pozinkovaný, nákup bez DPH (1.20–1.40 €/kg)
}

# ─────────────────────────────────────────────
#  VALCOVACÍ MODUL — plate roller (veľké rádiusy)
#  Logika: setup fee za nastavenie valcov na rádius
#           + cena za meter valcovanej dĺžky
# ─────────────────────────────────────────────
ROLLING_PARAMS = {
    # Setup fee za 1 nastavenie valcov (1 rádius)
    "setup_fee_per_radius_eur": 15.0,

    # Cena za meter valcovanej dĺžky podľa hrúbky (€/m)
    "price_per_meter_tiers": [
        {"max_thickness_mm": 3,  "price": 3.0},
        {"max_thickness_mm": 5,  "price": 4.0},
        {"max_thickness_mm": 8,  "price": 5.5},
        {"max_thickness_mm": 12, "price": 7.5},
        {"max_thickness_mm": 20, "price": 12.0},
        {"max_thickness_mm": 999,"price": 18.0},
    ],

    # Množstevný koeficient (séria = menej prestávok)
    "qty_factor_tiers": [
        {"max_qty": 1,    "factor": 2.0},   # prototyp — setup dominuje
        {"max_qty": 5,    "factor": 1.5},
        {"max_qty": 20,   "factor": 1.1},
        {"max_qty": 9999, "factor": 0.9},
    ],

    # Minimálna cena za sériu
    "min_order_eur": 25.0,
}


def calculate_rolling_price(rolls: list, thickness_mm: float, qty: int,
                             margin_pct: float = 20.0) -> dict:
    """
    Vypočíta cenu valcovania.

    rolls: [{"radius_mm": 3169, "length_mm": 1000}, ...]
    thickness_mm: hrúbka materiálu
    qty: počet kusov
    margin_pct: marža

    Každý unikátny rádius = 1 nastavenie valcov (setup fee).
    """
    if not rolls:
        return {"rolling_applicable": False, "rolling_total": 0.0}

    # Cena za meter podľa hrúbky
    price_per_m = ROLLING_PARAMS["price_per_meter_tiers"][-1]["price"]
    for tier in ROLLING_PARAMS["price_per_meter_tiers"]:
        if thickness_mm <= tier["max_thickness_mm"]:
            price_per_m = tier["price"]
            break

    # Množstevný koeficient
    qty_factor = ROLLING_PARAMS["qty_factor_tiers"][-1]["factor"]
    for tier in ROLLING_PARAMS["qty_factor_tiers"]:
        if qty <= tier["max_qty"]:
            qty_factor = tier["factor"]
            break

    # Počet unikátnych rádiusov = počet prestavení
    unique_radii = len(set(r.get("radius_mm", 0) for r in rolls))
    setup_total = unique_radii * ROLLING_PARAMS["setup_fee_per_radius_eur"]
    setup_per_piece = setup_total / qty

    # Cena valcovania per piece
    total_length_m = sum(float(r.get("length_mm", 0)) for r in rolls) / 1000
    rolling_cost_per_piece = total_length_m * price_per_m * qty_factor

    # Celková cena netto/ks
    rolling_net_per_piece = rolling_cost_per_piece + setup_per_piece

    # S maržou
    rolling_sell_per_piece = rolling_net_per_piece * (1 + margin_pct / 100)
    rolling_total = rolling_sell_per_piece * qty
    rolling_total = max(rolling_total, ROLLING_PARAMS["min_order_eur"])

    return {
        "rolling_applicable": True,
        "roll_count": len(rolls),
        "unique_radii": unique_radii,
        "total_length_m": round(total_length_m, 3),
        "price_per_m": round(price_per_m, 2),
        "qty_factor": qty_factor,
        "setup_total": round(setup_total, 2),
        "setup_per_piece": round(setup_per_piece, 3),
        "rolling_cost_per_piece": round(rolling_cost_per_piece, 3),
        "rolling_net_per_piece": round(rolling_net_per_piece, 3),
        "rolling_sell_per_piece": round(rolling_sell_per_piece, 2),
        "rolling_total": round(rolling_total, 2),
    }


# ─────────────────────────────────────────────
#  OHYBÁRSKY MODUL — CNC ohraňovací lis
#  Ceny platné pre GRYF KOMBI (TecKon)
#  Logika: setup fee (fixný) + cena/ohyb (stupňovaná podľa qty)
# ─────────────────────────────────────────────
BENDING_PARAMS = {
    # Fixný setup fee za sériu (nastavenie zarážok, programovanie)
    "setup_fee_eur": 8.0,

    # Cena za 1 ohyb podľa množstva kusov v sérii
    # Formát: {max_qty: price_per_bend_eur}  — platí pre qty <= max_qty
    # Príklad: 1-5ks = 0.90€/ohyb, 6-20ks = 0.65€, 21-50ks = 0.45€, 51+ = 0.32€
    "price_per_bend_tiers": [
        {"max_qty": 5,   "price": 0.90},
        {"max_qty": 20,  "price": 0.65},
        {"max_qty": 50,  "price": 0.45},
        {"max_qty": 9999,"price": 0.32},
    ],

    # Príplatky za zložitosť ohybu (multiplicatívne na cenu/ohyb)
    # Závisí od dĺžky ohybovej hrany (mm)
    "length_surcharge": [
        {"max_length_mm": 500,  "factor": 1.0},   # štandard
        {"max_length_mm": 1000, "factor": 1.15},  # dlhý ohyb (presnosť)
        {"max_length_mm": 9999, "factor": 1.30},  # veľmi dlhý
    ],

    # Príplatok za hmotnosť dielu pri ohýbaní
    # Ťažší diel = pomalšie polohovaný, niekedy 2 operátori
    "weight_surcharge": [
        {"max_kg": 5,    "factor": 1.0,  "label": None},
        {"max_kg": 15,   "factor": 1.10, "label": "×1.10 (5–15kg — pomalšie polohovanie)"},
        {"max_kg": 30,   "factor": 1.20, "label": "×1.20 (15–30kg — 2 operátori)"},
        {"max_kg": 9999, "factor": 1.35, "label": "×1.35 (>30kg — žeriav)"},
    ],
}


def calculate_bending_price(bends: list, qty: int, margin_pct: float = 20.0,
                            weight_kg: float = 0.0) -> dict:
    """
    Vypočíta cenu ohýbania pre zoznam ohybov.

    bends:     [{"angle_deg": 90, "radius_mm": 2, "length_mm": 200}, ...]
    qty:       počet kusov v sérii
    margin_pct: marža na ohýbanie (%)
    weight_kg: čistá hmotnosť dielu (kg) — pre hmotnostný príplatok
    """
    if not bends:
        return {"bending_applicable": False, "bending_total": 0.0}

    bend_count = len(bends)

    # Cena za ohyb podľa qty tieru
    price_per_bend = BENDING_PARAMS["price_per_bend_tiers"][-1]["price"]
    for tier in BENDING_PARAMS["price_per_bend_tiers"]:
        if qty <= tier["max_qty"]:
            price_per_bend = tier["price"]
            break

    # Setup fee (rozdelený na sériu)
    setup_fee_total = BENDING_PARAMS["setup_fee_eur"]
    setup_fee_per_piece = setup_fee_total / qty

    # Hmotnostný koeficient
    weight_factor = 1.0
    weight_label = None
    for ws in BENDING_PARAMS["weight_surcharge"]:
        if weight_kg <= ws["max_kg"]:
            weight_factor = ws["factor"]
            weight_label = ws["label"]
            break

    # Cena ohybov s príplatkami za dĺžku + hmotnostný faktor
    bending_cost_per_piece = 0.0
    bend_detail = []
    for b in bends:
        length = float(b.get("length_mm", 500))
        angle = float(b.get("angle_deg", 90))

        # Príplatok za dĺžku ohybu
        length_factor = 1.0
        for ls in BENDING_PARAMS["length_surcharge"]:
            if length <= ls["max_length_mm"]:
                length_factor = ls["factor"]
                break

        cost = price_per_bend * length_factor * weight_factor
        bending_cost_per_piece += cost
        bend_detail.append({
            "angle_deg": angle,
            "length_mm": length,
            "length_factor": length_factor,
            "cost_eur": round(cost, 3),
        })

    # Predajná cena (s maržou)
    bending_cost_net = bending_cost_per_piece + setup_fee_per_piece
    bending_sell_per_piece = bending_cost_net * (1 + margin_pct / 100)
    bending_total = bending_sell_per_piece * qty

    return {
        "bending_applicable": True,
        "bend_count": bend_count,
        "price_per_bend": round(price_per_bend, 3),
        "weight_kg": round(weight_kg, 3),
        "weight_factor": weight_factor,
        "weight_label": weight_label,
        "setup_fee_total": round(setup_fee_total, 2),
        "setup_fee_per_piece": round(setup_fee_per_piece, 3),
        "bending_cost_per_piece": round(bending_cost_per_piece, 3),
        "bending_cost_net": round(bending_cost_net, 3),
        "bending_sell_per_piece": round(bending_sell_per_piece, 2),
        "bending_total": round(bending_total, 2),
        "bend_detail": bend_detail,
    }


# Hustota kg/m³
MATERIAL_DENSITY = {
    "ocel":  7850,
    "nerez": 7900,
    "hlinik": 2700,
    "pozink": 7850,  # rovnaká hustota ako oceľ
}


def get_cutting_speed(material, thickness):
    """Interpolácia reznej rýchlosti pre zadanú hrúbku."""
    speeds = CUTTING_SPEEDS.get(material, CUTTING_SPEEDS["ocel"])
    thicknesses = sorted(speeds.keys())

    if thickness <= thicknesses[0]:
        return speeds[thicknesses[0]]
    if thickness >= thicknesses[-1]:
        return speeds[thicknesses[-1]]

    # lineárna interpolácia
    for i in range(len(thicknesses) - 1):
        t1, t2 = thicknesses[i], thicknesses[i+1]
        if t1 <= thickness <= t2:
            v1, v2 = speeds[t1], speeds[t2]
            return v1 + (v2 - v1) * (thickness - t1) / (t2 - t1)

    return speeds[thicknesses[-1]]


def get_pierce_time(material, thickness):
    """Interpolácia času prepichnutia podľa materiálu a hrúbky."""
    times = PIERCE_TIME.get(material, PIERCE_TIME["ocel"])
    thicknesses = sorted(times.keys())
    if thickness <= thicknesses[0]:
        return times[thicknesses[0]]
    if thickness >= thicknesses[-1]:
        return times[thicknesses[-1]]
    for i in range(len(thicknesses) - 1):
        t1, t2 = thicknesses[i], thicknesses[i+1]
        if t1 <= thickness <= t2:
            p1, p2 = times[t1], times[t2]
            return p1 + (p2 - p1) * (thickness - t1) / (t2 - t1)
    return times[thicknesses[-1]]


def extract_dxf_geometry(filepath):
    """
    Načíta DXF a vráti:
      - cut_length_mm: celková dĺžka rezu v mm
      - area_mm2: plocha ohraničujúceho obdĺžnika (bounding box) v mm²
      - pierce_count: počet prepichnutí (uzavreté kontúry)
      - entity_counts: počet entít podľa typu
    """
    doc = ezdxf.readfile(filepath)
    msp = doc.modelspace()

    total_length = 0.0
    pierce_count = 0
    entity_counts = {}

    # Zistíme jednotky DXF (default mm)
    units = doc.header.get('$INSUNITS', 4)  # 4 = mm
    scale = 1.0
    if units == 1:   scale = 25.4    # inches → mm
    elif units == 2: scale = 304.8   # feet → mm
    elif units == 4: scale = 1.0     # mm
    elif units == 5: scale = 10.0    # cm → mm
    elif units == 6: scale = 1000.0  # m → mm

    min_x = min_y = float('inf')
    max_x = max_y = float('-inf')

    def update_bbox(x, y):
        nonlocal min_x, min_y, max_x, max_y
        min_x = min(min_x, x)
        min_y = min(min_y, y)
        max_x = max(max_x, x)
        max_y = max(max_y, y)

    for entity in msp:
        etype = entity.dxftype()
        entity_counts[etype] = entity_counts.get(etype, 0) + 1

        try:
            if etype == 'LINE':
                s = entity.dxf.start
                e = entity.dxf.end
                length = math.sqrt((e.x-s.x)**2 + (e.y-s.y)**2) * scale
                total_length += length
                update_bbox(s.x * scale, s.y * scale)
                update_bbox(e.x * scale, e.y * scale)

            elif etype == 'ARC':
                r = entity.dxf.radius * scale
                start_angle = math.radians(entity.dxf.start_angle)
                end_angle = math.radians(entity.dxf.end_angle)
                if end_angle < start_angle:
                    end_angle += 2 * math.pi
                arc_length = r * (end_angle - start_angle)
                total_length += arc_length
                # bbox approx
                cx = entity.dxf.center.x * scale
                cy = entity.dxf.center.y * scale
                update_bbox(cx - r, cy - r)
                update_bbox(cx + r, cy + r)
                pierce_count += 1  # každý oblúk = potenciálny otvor

            elif etype == 'CIRCLE':
                r = entity.dxf.radius * scale
                total_length += 2 * math.pi * r
                cx = entity.dxf.center.x * scale
                cy = entity.dxf.center.y * scale
                update_bbox(cx - r, cy - r)
                update_bbox(cx + r, cy + r)
                pierce_count += 1

            elif etype == 'LWPOLYLINE':
                points = list(entity.get_points())
                is_closed = entity.closed
                if len(points) >= 2:
                    for i in range(len(points) - 1):
                        x1, y1 = points[i][0] * scale, points[i][1] * scale
                        x2, y2 = points[i+1][0] * scale, points[i+1][1] * scale
                        # bulge pre oblúky
                        bulge = points[i][4] if len(points[i]) > 4 else 0
                        if bulge != 0:
                            chord = math.sqrt((x2-x1)**2 + (y2-y1)**2)
                            sagitta = abs(bulge) * chord / 2
                            r = (chord**2 + 4*sagitta**2) / (8*sagitta) if sagitta > 0 else chord/2
                            angle = 4 * math.atan(abs(bulge))
                            seg_length = r * angle
                        else:
                            seg_length = math.sqrt((x2-x1)**2 + (y2-y1)**2)
                        total_length += seg_length
                        update_bbox(x1, y1)
                        update_bbox(x2, y2)
                    if is_closed and len(points) >= 3:
                        x1, y1 = points[-1][0] * scale, points[-1][1] * scale
                        x2, y2 = points[0][0] * scale, points[0][1] * scale
                        total_length += math.sqrt((x2-x1)**2 + (y2-y1)**2)
                        pierce_count += 1

            elif etype == 'SPLINE':
                pts = list(entity.flattening(0.1))
                for i in range(len(pts) - 1):
                    dx = (pts[i+1][0] - pts[i][0]) * scale
                    dy = (pts[i+1][1] - pts[i][1]) * scale
                    total_length += math.sqrt(dx**2 + dy**2)
                if pts:
                    update_bbox(pts[0][0]*scale, pts[0][1]*scale)
                    update_bbox(pts[-1][0]*scale, pts[-1][1]*scale)

            elif etype == 'ELLIPSE':
                # aproximácia obvodu elipsy
                major = entity.dxf.major_axis
                a = math.sqrt(major.x**2 + major.y**2) * scale
                b = a * entity.dxf.ratio
                # Ramanujan aproximácia
                h = ((a-b)/(a+b))**2
                perimeter = math.pi * (a+b) * (1 + 3*h/(10 + math.sqrt(4-3*h)))
                total_length += perimeter
                pierce_count += 1

        except Exception:
            pass  # preskočíme entity s chýbajúcimi atribútmi

    # Bounding box plocha
    if min_x == float('inf'):
        area_mm2 = 0
        bbox = (0, 0, 0, 0)
    else:
        width = max_x - min_x
        height = max_y - min_y
        area_mm2 = width * height
        bbox = (round(min_x,1), round(min_y,1), round(max_x,1), round(max_y,1))

    return {
        "cut_length_mm": round(total_length, 1),
        "area_mm2": round(area_mm2, 1),
        "pierce_count": max(pierce_count, 1),  # min 1 prepichnutie
        "entity_counts": entity_counts,
        "bbox": bbox,
        "bbox_width_mm": round(max_x - min_x, 1) if min_x != float('inf') else 0,
        "bbox_height_mm": round(max_y - min_y, 1) if min_y != float('inf') else 0,
    }


def calculate_price(geometry, params):
    """
    Vypočíta cenu výpalku.
    params: material, thickness_mm, quantity, hourly_rate,
            setup_time_min, margin_pct, material_price_override
    """
    mat = params["material"]
    t = float(params["thickness_mm"])
    qty = int(params["quantity"])
    hourly_rate = float(params.get("hourly_rate", 80))
    setup_time_min = float(params.get("setup_time_min", 10))
    margin_pct = float(params.get("margin_pct", 20))
    mat_price_kg_buy = float(params.get("material_price_kg") or MATERIAL_PRICE_PER_KG.get(mat, 1.0))
    mat_margin_pct = float(params.get("material_margin_pct", 20))
    scrap_factor = float(params.get("scrap_factor", 1.25))
    shape_factor = float(params.get("shape_factor", 1.0))  # korekcia plochy pre zložité tvary
    holes = params.get("holes", [])  # [{diameter_mm, count}, ...] z AI analýzy
    powder_coating = bool(params.get("powder_coating", False))
    powder_coating_price = float(params.get("powder_coating_price", 14.0))  # €/m² základ
    powder_oven_capacity_m2 = float(params.get("powder_oven_capacity_m2", 40.0))  # m² na 1 takt pece
    powder_oven_cost = float(params.get("powder_oven_cost", 45.0))  # € réžia za 1 takt pece
    powder_min_order = float(params.get("powder_min_order", 45.0))  # € minimálna objednávka

    # Predajná cena materiálu
    mat_price_kg_sell = mat_price_kg_buy * (1 + mat_margin_pct / 100)

    # ── A. DETEKCIA MINIATÚRNYCH DIER ────────────────────────────────
    # Pravidlo: priemer diery < hrúbka plechu → laser nevyrežie, treba vŕtať
    DRILL_SURCHARGE = 0.50  # €/diera
    small_holes = []
    drill_cost = 0.0
    for h in holes:
        d = float(h.get("diameter_mm", 99))
        cnt = int(h.get("count", 1))
        if d < t:
            small_holes.append({"diameter_mm": d, "count": cnt})
            drill_cost += cnt * DRILL_SURCHARGE

    # ── C. INTELIGENTNÝ VÝBER REZNÉHO PLYNU ──────────────────────────
    gas_info = select_gas(mat, t)

    cut_length_m = geometry["cut_length_mm"] / 1000
    pierce_count = geometry["pierce_count"]
    bbox_w = geometry.get("bbox_width_mm", 500)
    bbox_h = geometry.get("bbox_height_mm", 500)
    max_dim = max(bbox_w, bbox_h)

    # Medzera medzi dielmi pri nestingu (kerf + tepelná zóna)
    nesting_gap = max(5.0, 2.0 * t)
    area_with_gap_mm2 = (bbox_w + nesting_gap) * (bbox_h + nesting_gap)
    area_m2 = area_with_gap_mm2 / 1e6

    # Rezná rýchlosť (tabuľková)
    speed_m_min = get_cutting_speed(mat, t)

    # Čistý čas rezania × safety factor 1.35
    # (korekcia: akcelerácia v rohoch, optické korekcie, spomalenie pri malých tvaroch)
    safety = MACHINE_PARAMS["cutting_safety_factor"]
    cutting_time_min = (cut_length_m / speed_m_min) * safety

    # Počet vnútorných kontúr = pierce_count - 1 (vonkajší obrys nie je frog jump)
    inner_contours = max(pierce_count - 1, 0)

    # Čas prepalov (veľmi krátke pri 12kW — FlyCut pre tenké materiály)
    pierce_time_sec = pierce_count * get_pierce_time(mat, t)
    pierce_time_min = pierce_time_sec / 60

    # Frog Jump: zdvih hlavy, presun, spust pri každej vnútornej kontúre
    frog_jump_sec = inner_contours * MACHINE_PARAMS["frog_jump_sec"]
    rapid_time_min = frog_jump_sec / 60

    # Minimálny strojový čas na kus
    min_machine_time_min = MACHINE_PARAMS["min_machine_time_min"]

    raw_machine_time = cutting_time_min + pierce_time_min + rapid_time_min
    machine_time_per_piece_min = max(raw_machine_time, min_machine_time_min)

    # Efektívna rýchlosť (pre zobrazenie — spätný výpočet)
    effective_speed = cut_length_m / cutting_time_min if cutting_time_min > 0 else speed_m_min
    efficiency = round(1 / safety * 100)

    # Nastavovací čas (rozdelený na sériu)
    setup_time_per_piece_min = setup_time_min / qty

    total_time_per_piece_min = machine_time_per_piece_min + setup_time_per_piece_min

    # Náklady na stroj (základné)
    machine_cost_per_piece = (total_time_per_piece_min / 60) * hourly_rate

    # ── C. NÁKLADY NA REZNÝ PLYN ─────────────────────────────────────
    cutting_time_sec = cutting_time_min * 60
    gas_cost_per_piece = cutting_time_sec * gas_info["cost_per_sec"]

    # ── B. KOEFICIENT MANIPULÁCIE (váhový príplatok) ─────────────────
    # Vypočítame čistú hmotnosť pre rozhodnutie (pred scrap faktorom)
    density_tmp = MATERIAL_DENSITY.get(mat, 7850)
    nesting_gap_tmp = max(5.0, 2.0 * t)
    area_m2_tmp = ((geometry.get("bbox_width_mm",100) + nesting_gap_tmp) *
                   (geometry.get("bbox_height_mm",100) + nesting_gap_tmp)) / 1e6
    weight_for_handling = area_m2_tmp * (t / 1000) * density_tmp

    if weight_for_handling > 40:
        handling_factor = 2.0    # 2 ľudia / žeriav
        handling_label = "×2.0 (>40kg — žeriav)"
    elif weight_for_handling > 20:
        handling_factor = 1.5    # 2 ľudia
        handling_label = "×1.5 (>20kg — 2 operátori)"
    else:
        handling_factor = 1.0
        handling_label = None

    # Príplatok za manipuláciu = rozdiel oproti normálnym nákladom
    handling_surcharge = machine_cost_per_piece * (handling_factor - 1.0)

    # Materiál — hmotnosti
    density = MATERIAL_DENSITY.get(mat, 7850)
    thickness_m = t / 1000

    # Čistá hmotnosť = iba samotný diel × shape_factor (korekcia pre zložité tvary)
    area_m2_pure = (bbox_w * bbox_h) / 1e6 * shape_factor
    weight_kg_net = area_m2_pure * thickness_m * density

    # Billed hmotnosť = s nesting medzerou + scrap faktor (pre výpočet ceny materiálu)
    # shape_factor sa aplikuje aj na materiálové náklady
    weight_kg_billed = area_m2 * shape_factor * thickness_m * density * scrap_factor

    # Náklady materiálu = billed hmotnosť × predajná cena (s maržou na materiál)
    material_cost = weight_kg_billed * mat_price_kg_sell

    material_cost_buy = weight_kg_billed * mat_price_kg_buy
    material_margin_eur = material_cost - material_cost_buy

    # ── PRÁŠKOVÁ FARBA ───────────────────────────────────────────────
    powder_area_per_piece_m2 = area_m2 * 2  # obe strany rozvinutého tvaru
    powder_area_total_m2 = powder_area_per_piece_m2 * qty

    if powder_coating:
        # 1. Množstevný koeficient (efektivita striekania)
        if qty == 1:
            powder_qty_factor = 2.0
        elif qty <= 10:
            powder_qty_factor = 1.5
        elif qty <= 50:
            powder_qty_factor = 1.1
        elif qty <= 200:
            powder_qty_factor = 0.9
        else:
            powder_qty_factor = 0.75

        # 2. Cena za plochu (celá séria)
        powder_area_cost_total = powder_area_total_m2 * powder_coating_price * powder_qty_factor

        # 3. Réžia pece — počet taktov × fixná réžia
        powder_oven_cycles = math.ceil(powder_area_total_m2 / powder_oven_capacity_m2)
        powder_oven_cost_total = powder_oven_cycles * powder_oven_cost

        # 4. Celková cena lakovania
        powder_total = powder_area_cost_total + powder_oven_cost_total
        powder_total = max(powder_total, powder_min_order)  # minimálna objednávka

        powder_cost_per_piece = powder_total / qty
    else:
        powder_qty_factor = 1.0
        powder_oven_cycles = 0
        powder_oven_cost_total = 0.0
        powder_total = 0.0
        powder_cost_per_piece = 0.0

    # Vlastné náklady = stroj + plyn + manipulácia + materiál (nákup) + vŕtanie + prášok
    cost_per_piece = (machine_cost_per_piece + gas_cost_per_piece +
                      handling_surcharge + material_cost_buy + drill_cost + powder_cost_per_piece)

    # Predajná cena = (stroj + plyn + manipulácia) s maržou + materiál s mat.maržou + vŕtanie + prášok
    machine_total = (machine_cost_per_piece + gas_cost_per_piece + handling_surcharge)
    machine_sell = machine_total * (1 + margin_pct / 100)
    price_per_piece = machine_sell + material_cost + drill_cost + powder_cost_per_piece
    price_total = price_per_piece * qty

    return {
        "speed_m_min": round(speed_m_min, 1),
        "effective_speed_m_min": round(effective_speed, 1),
        "efficiency_pct": efficiency,
        "nesting_gap_mm": round(nesting_gap, 1),
        "area_with_gap_mm2": round(area_with_gap_mm2, 1),
        "cutting_time_min": round(cutting_time_min, 3),
        "pierce_time_min": round(pierce_time_min, 3),
        "rapid_time_min": round(rapid_time_min, 3),
        "machine_time_per_piece_min": round(machine_time_per_piece_min, 3),
        "setup_time_per_piece_min": round(setup_time_per_piece_min, 2),
        "total_time_per_piece_min": round(total_time_per_piece_min, 2),
        "machine_cost_per_piece": round(machine_cost_per_piece, 3),
        # Materiál
        "weight_kg_net": round(weight_kg_net, 3),
        "weight_kg_billed": round(weight_kg_billed, 3),
        "scrap_factor": scrap_factor,
        "shape_factor": shape_factor,
        "mat_price_kg_buy": round(mat_price_kg_buy, 3),
        "mat_price_kg_sell": round(mat_price_kg_sell, 3),
        "mat_margin_pct": mat_margin_pct,
        "material_cost_buy": round(material_cost_buy, 3),
        "material_cost_sell": round(material_cost, 3),
        "material_margin_eur": round(material_margin_eur, 3),
        # Plyn
        "gas": gas_info["gas"],
        "gas_cost_per_piece": round(gas_cost_per_piece, 3),
        # Manipulácia
        "weight_for_handling": round(weight_for_handling, 2),
        "handling_factor": handling_factor,
        "handling_label": handling_label,
        "handling_surcharge": round(handling_surcharge, 3),
        # Miniatúrne diery
        "small_holes": small_holes,
        "drill_cost": round(drill_cost, 2),
        # Prášková farba
        "powder_coating": powder_coating,
        "powder_area_per_piece_m2": round(powder_area_per_piece_m2, 4),
        "powder_area_total_m2": round(powder_area_total_m2, 4),
        "powder_qty_factor": powder_qty_factor,
        "powder_oven_cycles": powder_oven_cycles,
        "powder_oven_cost_total": round(powder_oven_cost_total, 2),
        "powder_total": round(powder_total, 2),
        "powder_cost_per_piece": round(powder_cost_per_piece, 2),
        # Celkové
        "cost_per_piece": round(cost_per_piece, 3),
        "margin_pct": margin_pct,
        "price_per_piece": round(price_per_piece, 2),
        "price_total": round(price_total, 2),
        "hourly_rate": hourly_rate,
    }


@app.route('/')
def index():
    return render_template('index.html')


@app.route('/config')
def config_page():
    return render_template('config.html',
        cutting_speeds=CUTTING_SPEEDS,
        pierce_time=PIERCE_TIME,
        machine_params=MACHINE_PARAMS,
        material_price=MATERIAL_PRICE_PER_KG,
    )


@app.route('/config/save', methods=['POST'])
def config_save():
    global CUTTING_SPEEDS, PIERCE_TIME, MACHINE_PARAMS, MATERIAL_PRICE_PER_KG
    data = request.get_json()
    try:
        # Rezné rýchlosti
        for mat in ['ocel', 'nerez', 'hlinik']:
            if mat in data.get('speeds', {}):
                CUTTING_SPEEDS[mat] = {int(k): float(v)
                                       for k, v in data['speeds'][mat].items() if v != ''}
        # Časy prepichnutia
        if 'pierce' in data:
            PIERCE_TIME = {int(k): float(v)
                           for k, v in data['pierce'].items() if v != ''}
        # Parametre stroja
        if 'machine' in data:
            for k, v in data['machine'].items():
                if k in MACHINE_PARAMS:
                    MACHINE_PARAMS[k] = float(v)
        # Ceny materiálov
        if 'mat_price' in data:
            for k, v in data['mat_price'].items():
                if k in MATERIAL_PRICE_PER_KG:
                    MATERIAL_PRICE_PER_KG[k] = float(v)
        return jsonify({"ok": True})
    except Exception as e:
        return jsonify({"error": str(e)}), 400


@app.route('/upload-dxf', methods=['POST'])
def upload_dxf():
    if 'file' not in request.files:
        return jsonify({"error": "Žiadny súbor"}), 400

    f = request.files['file']
    if not f.filename.lower().endswith('.dxf'):
        return jsonify({"error": "Iba DXF súbory sú podporované"}), 400

    with tempfile.NamedTemporaryFile(delete=False, suffix='.dxf') as tmp:
        f.save(tmp.name)
        tmp_path = tmp.name

    try:
        geometry = extract_dxf_geometry(tmp_path)
        return jsonify({"ok": True, "geometry": geometry})
    except Exception as e:
        return jsonify({"error": str(e), "detail": traceback.format_exc()}), 500
    finally:
        os.unlink(tmp_path)


BOM_PROMPT = """Si expert na strojárenské výkresy a technickú dokumentáciu. Analyzuj priloženú výkresovú dokumentáciu zostavy a extrahuj BOM (Bill of Materials / zoznam dielov).

Vráť VÝLUČNE JSON objekt (žiadny iný text) v tomto formáte:
{
  "assembly_name": "<názov zostavy>",
  "drawing_number": "<číslo výkresu>",
  "total_mass_kg": <celková hmotnosť v kg alebo null>,
  "parts": [
    {
      "pos": <číslo pozície>,
      "part_number": "<číslo dielu>",
      "name": "<názov dielu>",
      "qty": <počet kusov>,
      "material": "<materiál>",
      "dimensions": "<rozmery napr. 460x318x10 alebo Ø30x25>",
      "mass_per_piece_kg": <hmotnosť 1ks v kg alebo null>,
      "total_mass_kg": <celková hmotnosť v kg alebo null>,
      "type": "laser|bought|weld|other",
      "remarks": "<poznámky>"
    }
  ]
}

PRAVIDLÁ pre pole "type":
- "laser" = plechový diel ktorý treba vyrezať laserom (plech, oceľ, nerez, hliník)
- "bought" = nakúpený normalizovaný diel (skrutky, matice, podložky, pružiny, ložiská, profily)
- "weld" = zvarovaná zostava
- "other" = iné

KRITICKÉ:
- Prečítaj CELÚ BOM tabuľku z výkresu — všetky riadky!
- Rozmery zapisuj presne ako sú v tabuľke (napr. "8x1669x60" = hrúbka x šírka x dĺžka)
- Ak materiál obsahuje EN normu (napr. "EN 10025-2 / 1.0577 / S355J2"), zaznamenej celý reťazec
- Hmotnosti zapisuj v kg (nie g)
- Ak niečo nie je jasné, daj null"""


VISION_PROMPT = """Si expert na strojárenské výkresy a výrobu z plechu. Analyzuj priložený technický výkres a extrahuj VŠETKY potrebné informácie pre kalkuláciu ceny laserového rezania.

Vráť VÝLUČNE JSON objekt (žiadny iný text) v tomto formáte:
{
  "material": "ocel|nerez|hlinik",
  "thickness_mm": <číslo>,
  "part_description": "<stručný popis dielu>",
  "flat_pattern": {
    "width_mm": <šírka ROZVINUTÉHO/ROZLOŽENÉHO tvaru v mm — NIE ohnutého dielu!>,
    "height_mm": <výška ROZVINUTÉHO/ROZLOŽENÉHO tvaru v mm — NIE ohnutého dielu!>,
    "cut_length_mm": <celková dĺžka rezu vrátane otvorov v mm>,
    "pierce_count": <počet otvorov/prepichnutí>
  },
  "bends": [
    {"angle_deg": <uhol>, "radius_mm": <polomer>, "length_mm": <dĺžka ohybu>}
  ],
  "holes": [
    {"diameter_mm": <priemer>, "count": <počet>}
  ],
  "notes": "<poznámky, nejasnosti, predpoklady — UVEĎ medzivýpočty rozvinutia>",
  "confidence": "high|medium|low"
}

KRITICKÉ PRAVIDLÁ:
- Rozmery dielu sú v MILIMETROCH (mm) — nie v metroch ani centimetroch!
- IGNORUJ formát papiera (A4, A3) — zaujíma ťa IBA samotný diel
- Typické rozmery plechových dielov: 10mm až 2000mm. Ak by rozmer vyšiel >3000mm, pravdepodobne si pomýlil jednotky
- Ak je v titulnom bloku (rohové políčko) výkresu uvedený rozvin polotovaru (napr. "252x873" alebo "Rohling", "Blank", "Polotovar"), použi TIETO hodnoty priamo ako flat_pattern.width_mm a flat_pattern.height_mm — sú najpresnejšie!

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 ROZVIN (FLAT PATTERN) — NAJDÔLEŽITEJŠIE PRAVIDLO
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
flat_pattern.width_mm a flat_pattern.height_mm MUSIA byť rozmery ROZVINUTÉHO PLECHU
(ako keby si diel úplne rozložil/narovnal do roviny). NIKDY nedávaj rozmery ohnutého dielu!

VZORCE (K-faktor = 0.45):
  BA = π/2 × (R + 0.45 × t)       ← bend allowance
  BD = 2 × (R + t) - BA            ← bend deduction
  Rozvin = súčet všetkých úsekov - (počet ohybov × BD)   ← pri vonkajších kótach
  Rozvin = súčet všetkých úsekov + (počet ohybov × BA)   ← pri vnútorných kótach

Príklady SPRÁVNEHO rozvinutia:

1) L-profil (1 ohyb), vonkajšie kóty: rameno_A=40, rameno_B=30, t=2, R=2
   → BA=4.555mm, BD=3.445mm
   → Rozvin = (40+30) - 1×3.445 = 66.6mm
   ❌ CHYBA: dať bounding box ohnutého L (napr. 40×30mm)

2) Z-profil (2 ohyby), vonkajšie kóty: horné=16.5, stojina=163, dolné=28.5, t=1.5, R=1.5
   → BA=3.415mm, BD=2.585mm
   → Rozvin = (16.5+163+28.5) - 2×2.585 = 202.8mm  ← flat_pattern šírka
   ❌ CHYBA: dať 47.5mm (bounding box ohnutého Z)

3) U-profil (2 ohyby), vonkajšie kóty: ramená=25, dno=80, t=3, R=3
   → BA=6.832mm, BD=5.168mm
   → Rozvin = (25+80+25) - 2×5.168 = 119.7mm

4) Hat/Omega profil so spodnými prírubami (4 ohyby) — TOTO JE DÔLEŽITÉ!
   Príklad: príruby=35, steny=188, veko=200, t=2, R=2 (všetko vonkajšie kóty)
   → BA = π/2×(2+0.45×2) = 4.555mm, BD = 2×(2+2)-4.555 = 3.445mm
   → Rozvin prierezu = 35+188+200+188+35 - 4×3.445 = 646 - 13.78 = 632.2mm  ← flat_pattern šírka
   → Dĺžka dielu (z výkresu, napr. 440mm) = flat_pattern výška
   → flat_pattern: 440 × 632mm
   ❌ CHYBA: dať 200×440mm (len veko bez stien a prírub)
   ❌ CHYBA: dať bounding box ohnutého hat-profilu (200×440mm alebo 258×440mm)
   ❌ CHYBA: zabudnúť na príruby — hat profil má 4 ohyby, nie 2!

5) Krabica/vaňa (4 ohyby), vonkajšie kóty: dno=150×200, výška stien=40, t=1.5, R=1.5
   → BD = 2×(1.5+1.5) - 3.415 = 2.585mm
   → Rozvin šírky = 40+150+40 - 2×2.585 = 225.2mm
   → Rozvin výšky = 40+200+40 - 2×2.585 = 275.2mm
   → flat_pattern: 225×275mm

POSTUP pre ohnutý diel:
1. Identifikuj TYP dielu a POČET OHYBOV:
   - L-profil = 1 ohyb, Z-profil = 2 ohyby, U-profil = 2 ohyby
   - Hat/Omega/U so prírubami = 4 ohyby (príruby + steny + veko)
   - Krabica/vaňa = 4 ohyby (v každom smere 2)
2. Skontroluj titulný blok výkresu — ak je tam "Blank/Rohling/Polotovar: AxB", použi to!
3. Prečítaj VŠETKY kóty pre daný prierez z výkresu (všetky úseky vrátane malých prírub!)
4. Zisti t (hrúbka) a R (ohybový polomer; ak nie je uvedený, predpokladaj R = t)
5. Vypočítaj BD, aplikuj na každý ohyb
6. Rozvin = suma VŠETKÝCH úsekov prierezu - počet_ohybov × BD
7. Dĺžka dielu (smer kolmý na ohyby) = nezmenená, zobrat z výkresu
8. flat_pattern.width_mm = rozvin prierezu, flat_pattern.height_mm = dĺžka dielu
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

- Ak materiál nie je uvedený, predpokladaj "nerez"
- Ak hrúbka nie je jasná, predpokladaj 2mm
- pierce_count = počet uzavretých otvorov + 1 (vonkajší obrys)
- cut_length_mm = obvod rozvinutého tvaru + súčet obvodov všetkých otvorov (π × d × počet)
- Do "notes" uveď výpočet krok po kroku: typ profilu, všetky úseky, BD, výsledný rozvin"""


def image_to_base64(image_path: str) -> tuple[str, str]:
    """Konvertuje obrázok na base64 a vráti (data, media_type)."""
    with open(image_path, 'rb') as f:
        data = f.read()
    # Detect media type
    if image_path.lower().endswith('.png'):
        media_type = 'image/png'
    elif image_path.lower().endswith(('.jpg', '.jpeg')):
        media_type = 'image/jpeg'
    elif image_path.lower().endswith('.gif'):
        media_type = 'image/gif'
    elif image_path.lower().endswith('.webp'):
        media_type = 'image/webp'
    else:
        media_type = 'image/png'
    return base64.standard_b64encode(data).decode('utf-8'), media_type


def analyze_drawing_with_claude(image_path: str) -> dict:
    """Pošle obrázok výkresu do Claude Vision a vráti extrahované údaje."""
    client = anthropic.Anthropic()

    img_b64, media_type = image_to_base64(image_path)

    message = client.messages.create(
        model="claude-opus-4-7",
        max_tokens=2048,
        messages=[
            {
                "role": "user",
                "content": [
                    {
                        "type": "image",
                        "source": {
                            "type": "base64",
                            "media_type": media_type,
                            "data": img_b64,
                        },
                    },
                    {
                        "type": "text",
                        "text": VISION_PROMPT
                    }
                ],
            }
        ],
    )

    response_text = message.content[0].text.strip()
    # Extrahuj JSON z odpovede
    if '```json' in response_text:
        response_text = response_text.split('```json')[1].split('```')[0].strip()
    elif '```' in response_text:
        response_text = response_text.split('```')[1].split('```')[0].strip()

    return json.loads(response_text)


def calc_bend_deduction(radius_mm: float, thickness_mm: float, angle_deg: float = 90, k_factor: float = 0.45) -> float:
    """Vypočíta Bend Deduction pre vonkajšie kóty."""
    angle_rad = math.radians(angle_deg)
    ba = angle_rad / 2 * (radius_mm + k_factor * thickness_mm)  # pre ľubovoľný uhol
    ossb = math.tan(angle_rad / 2) * (radius_mm + thickness_mm)
    return 2 * ossb - ba


def claude_result_to_geometry(claude_data: dict) -> dict:
    """Konvertuje výsledok z Claude na geometry formát pre kalkuláciu."""
    fp = claude_data.get("flat_pattern", {})
    w = float(fp.get("width_mm", 100))
    h = float(fp.get("height_mm", 100))
    cut_length = float(fp.get("cut_length_mm", 0))
    thickness = float(claude_data.get("thickness_mm", 2))

    # pierce_count: použi hodnotu z flat_pattern, ale over ju oproti zoznamu holes
    # Správne: 1 (vonkajší obrys) + počet uzavretých otvorov
    holes = claude_data.get("holes", [])
    holes_total_count = sum(int(hi.get("count", 1)) for hi in holes)
    pierce_from_fp = int(fp.get("pierce_count", 0))
    # Vezmi maximum — AI niekedy zabudne zarátať vonkajší obrys
    pierce_count = max(pierce_from_fp, holes_total_count + 1)

    # Ak flat_pattern rozmery nie sú zadané priamo, vypočítaj z ohybov
    bends = claude_data.get("bends", [])
    if bends and w > 0 and h > 0:
        # Claude vrátil rozmery ohnutého dielu (vonkajšie kóty) → aplikuj BD
        total_bd = sum(
            calc_bend_deduction(
                float(b.get("radius_mm", 1)),
                thickness,
                float(b.get("angle_deg", 90))
            ) for b in bends
        )
        # BD odčítame len ak sa zdá že rozmery nie sú ešte rozvinuté
        # (heuristika: ak je počet ohybov > 0 a rozmery zodpovedajú ohnutému dielu)
        w_flat = w - total_bd if len(bends) > 0 and w > h else w
        h_flat = h if w > h else h - total_bd
        # Použijeme hodnoty z Claude, opravené o BD
        # (Claude by mal vrátiť už rozvinutý tvar, ale pre istotu logujeme)
        print(f"  BD korekcia: {len(bends)} ohybov, celkový BD = {total_bd:.2f}mm")
        print(f"  Originál: {w}×{h}mm → po BD: {w_flat:.1f}×{h_flat:.1f}mm")

    # Ak cut_length nie je zadaná, odhadni z rozmerov
    if cut_length <= 0:
        holes = claude_data.get("holes", [])
        hole_length = sum(math.pi * hi.get("diameter_mm", 10) * hi.get("count", 1)
                          for hi in holes)
        cut_length = 2 * (w + h) + hole_length

    area_mm2 = w * h

    return {
        "cut_length_mm": round(cut_length, 1),
        "area_mm2": round(area_mm2, 1),
        "pierce_count": max(pierce_count, 1),
        "entity_counts": {"AI_VISION": 1},
        "bbox": (0, 0, round(w, 1), round(h, 1)),
        "bbox_width_mm": round(w, 1),
        "bbox_height_mm": round(h, 1),
    }


@app.route('/upload-pdf', methods=['POST'])
def upload_pdf():
    if 'file' not in request.files:
        return jsonify({"error": "Žiadny súbor"}), 400

    f = request.files['file']
    fname = f.filename.lower()
    allowed = ('.pdf', '.png', '.jpg', '.jpeg', '.tif', '.tiff', '.webp')
    if not any(fname.endswith(ext) for ext in allowed):
        return jsonify({"error": "Podporované formáty: PDF, PNG, JPG, TIF, WEBP"}), 400

    tmp_img_path = None
    tmp_orig_path = None

    try:
        suffix = os.path.splitext(fname)[1]
        with tempfile.NamedTemporaryFile(delete=False, suffix=suffix) as tmp:
            f.save(tmp.name)
            tmp_orig_path = tmp.name

        # Ak PDF — skonvertuj prvú stranu na PNG pomocou PyMuPDF (fitz)
        if fname.endswith('.pdf'):
            doc = fitz.open(tmp_orig_path)
            page = doc[0]
            # 200 DPI = scale 200/72 ≈ 2.78
            mat = fitz.Matrix(200 / 72, 200 / 72)
            pix = page.get_pixmap(matrix=mat, alpha=False)
            with tempfile.NamedTemporaryFile(delete=False, suffix='.png') as tmp_img:
                pix.save(tmp_img.name)
                tmp_img_path = tmp_img.name
            doc.close()
        elif fname.endswith(('.tif', '.tiff')):
            # Konvertuj TIF na PNG — s kompresiou ak je príliš veľký
            Image.MAX_IMAGE_PIXELS = None  # vypni ochranu pred veľkými TIF súbormi
            img = Image.open(tmp_orig_path)
            # Multi-page TIF — vezmi prvú stranu
            try:
                img.seek(0)
            except Exception:
                pass
            # Konvertuj do RGB (TIF môže byť CMYK alebo iný mód)
            if img.mode not in ('RGB', 'L'):
                img = img.convert('RGB')
            # Ak je obrázok príliš veľký, zmenši na max 3000px na dlhšej strane
            max_dim = 3000
            w_img, h_img = img.size
            if max(w_img, h_img) > max_dim:
                scale = max_dim / max(w_img, h_img)
                new_w = int(w_img * scale)
                new_h = int(h_img * scale)
                img = img.resize((new_w, new_h), Image.LANCZOS)
            with tempfile.NamedTemporaryFile(delete=False, suffix='.png') as tmp_img:
                img.save(tmp_img.name, 'PNG', optimize=True)
                tmp_img_path = tmp_img.name
        else:
            tmp_img_path = tmp_orig_path

        # Analýza s Claude Vision
        claude_data = analyze_drawing_with_claude(tmp_img_path)
        print("=== CLAUDE AI VÝSLEDOK ===")
        print(json.dumps(claude_data, indent=2, ensure_ascii=False))
        print("==========================")
        geometry = claude_result_to_geometry(claude_data)

        # Pridaj AI metadata k odpovedi
        return jsonify({
            "ok": True,
            "geometry": geometry,
            "ai_analysis": {
                "material": claude_data.get("material"),
                "thickness_mm": claude_data.get("thickness_mm"),
                "part_description": claude_data.get("part_description"),
                "bends": claude_data.get("bends", []),
                "holes": claude_data.get("holes", []),
                "notes": claude_data.get("notes"),
                "confidence": claude_data.get("confidence"),
            }
        })

    except json.JSONDecodeError as e:
        return jsonify({"error": f"Claude nevrátil validný JSON: {str(e)}"}), 500
    except anthropic.APIError as e:
        return jsonify({"error": f"Chyba Claude API: {str(e)}"}), 500
    except Exception as e:
        return jsonify({"error": str(e), "detail": traceback.format_exc()}), 500
    finally:
        for p in [tmp_orig_path, tmp_img_path]:
            if p and os.path.exists(p):
                try:
                    os.unlink(p)
                except Exception:
                    pass


@app.route('/upload-bom', methods=['POST'])
def upload_bom():
    """Nahrá výkres zostavy, Claude extrahuje BOM tabuľku."""
    if 'file' not in request.files:
        return jsonify({"error": "Žiadny súbor"}), 400

    f = request.files['file']
    fname = f.filename.lower()
    allowed = ('.pdf', '.png', '.jpg', '.jpeg', '.tif', '.tiff', '.webp')
    if not any(fname.endswith(ext) for ext in allowed):
        return jsonify({"error": "Podporované: PDF, PNG, JPG, TIF"}), 400

    tmp_img_path = None
    tmp_orig_path = None
    try:
        suffix = os.path.splitext(fname)[1]
        with tempfile.NamedTemporaryFile(delete=False, suffix=suffix) as tmp:
            f.save(tmp.name)
            tmp_orig_path = tmp.name

        # Konvertuj na PNG
        if fname.endswith('.pdf'):
            doc = fitz.open(tmp_orig_path)
            page = doc[0]
            mat = fitz.Matrix(200/72, 200/72)
            pix = page.get_pixmap(matrix=mat, alpha=False)
            with tempfile.NamedTemporaryFile(delete=False, suffix='.png') as ti:
                pix.save(ti.name)
                tmp_img_path = ti.name
            doc.close()
        elif fname.endswith(('.tif', '.tiff')):
            Image.MAX_IMAGE_PIXELS = None
            img = Image.open(tmp_orig_path)
            try: img.seek(0)
            except: pass
            if img.mode not in ('RGB', 'L'): img = img.convert('RGB')
            w_i, h_i = img.size
            if max(w_i, h_i) > 3000:
                scale = 3000 / max(w_i, h_i)
                img = img.resize((int(w_i*scale), int(h_i*scale)), Image.LANCZOS)
            with tempfile.NamedTemporaryFile(delete=False, suffix='.png') as ti:
                img.save(ti.name, 'PNG')
                tmp_img_path = ti.name
        else:
            tmp_img_path = tmp_orig_path

        # Pošli do Claude s BOM promptom
        client = anthropic.Anthropic()
        img_b64, media_type = image_to_base64(tmp_img_path)
        message = client.messages.create(
            model="claude-opus-4-7",
            max_tokens=4096,
            messages=[{
                "role": "user",
                "content": [
                    {"type": "image", "source": {"type": "base64",
                        "media_type": media_type, "data": img_b64}},
                    {"type": "text", "text": BOM_PROMPT}
                ]
            }]
        )
        raw = message.content[0].text.strip()
        # Vyčisti JSON
        if raw.startswith("```"):
            raw = raw.split("```")[1]
            if raw.startswith("json"): raw = raw[4:]
        raw = raw.strip()
        bom_data = json.loads(raw)

        print("=== BOM VÝSLEDOK ===")
        print(json.dumps(bom_data, indent=2, ensure_ascii=False))
        print("===================")

        return jsonify({"ok": True, "bom": bom_data})

    except json.JSONDecodeError as e:
        return jsonify({"error": f"Claude nevrátil validný JSON: {str(e)}"}), 500
    except anthropic.APIError as e:
        return jsonify({"error": f"Claude API chyba: {str(e)}"}), 500
    except Exception as e:
        return jsonify({"error": str(e), "detail": traceback.format_exc()}), 500
    finally:
        for p in [tmp_orig_path, tmp_img_path]:
            if p and os.path.exists(p):
                try: os.unlink(p)
                except: pass


def parse_dimensions(dim_str: str, material: str = "ocel") -> dict:
    """
    Parsuje reťazec rozmerov z BOM tabuľky na geometry dict.
    Príklady: "460x318x10", "8x1669x60", "Ø30x25", "1669x60x8"
    Vracia: {bbox_width_mm, bbox_height_mm, cut_length_mm, pierce_count, thickness_mm}
    """
    import re
    dim_str = dim_str.strip().upper()

    # Kruhový prierez: Ø30x25 alebo D30x25
    circ = re.match(r'[ØDO](\d+\.?\d*)[Xx](\d+\.?\d*)', dim_str)
    if circ:
        d = float(circ.group(1))
        length = float(circ.group(2))
        cut_length = math.pi * d + 2 * length
        return {
            "bbox_width_mm": d, "bbox_height_mm": length,
            "cut_length_mm": round(cut_length, 1),
            "pierce_count": 1, "thickness_mm": d,
        }

    # Extrahuj čísla z reťazca
    nums = [float(x) for x in re.findall(r'\d+\.?\d*', dim_str) if float(x) > 0]
    if not nums:
        return {"bbox_width_mm": 100, "bbox_height_mm": 100,
                "cut_length_mm": 400, "pierce_count": 1, "thickness_mm": 2}

    if len(nums) == 1:
        # Len jedna hodnota — predpokladaj štvorec
        return {"bbox_width_mm": nums[0], "bbox_height_mm": nums[0],
                "cut_length_mm": 4 * nums[0], "pierce_count": 1, "thickness_mm": nums[0]}

    if len(nums) == 2:
        # Dva rozmery — hrúbka nie je jasná, predpokladaj štandardnú
        w, h = sorted(nums, reverse=True)
        t = 2.0
        cut = 2 * (w + h)
        return {"bbox_width_mm": w, "bbox_height_mm": h,
                "cut_length_mm": round(cut, 1), "pierce_count": 1, "thickness_mm": t}

    # Tri rozmery: najmenší = hrúbka, zvyšné = rozmery polotovaru
    nums_sorted = sorted(nums)
    t = nums_sorted[0]
    dims = sorted(nums_sorted[1:], reverse=True)
    w, h = dims[0], dims[1] if len(dims) > 1 else dims[0]
    cut = 2 * (w + h)
    return {
        "bbox_width_mm": w, "bbox_height_mm": h,
        "cut_length_mm": round(cut, 1),
        "pierce_count": 1, "thickness_mm": t,
    }


@app.route('/calculate-bom-batch', methods=['POST'])
def calculate_bom_batch():
    """Batch kalkulácia pre všetky laser diely z BOM."""
    data = request.get_json()
    parts = data.get("parts", [])        # laser diely z BOM
    default_params = data.get("params", {})  # spoločné parametre (hourly_rate, margin...)

    results = []
    for p in parts:
        try:
            dim_str   = p.get("dimensions", "")
            mat_str   = (p.get("material", "")).lower()
            qty       = int(p.get("qty", 1))

            # Zisti materiál
            mat = "ocel"
            for key, val in [("1.4301","nerez"),("1.4307","nerez"),("x5crni","nerez"),
                              ("almg","hlinik"),("al99","hlinik"),("en aw","hlinik"),
                              ("dx51","pozink"),("s235","ocel"),("s355","ocel"),
                              ("dc01","ocel"),("dc04","ocel")]:
                if key in mat_str:
                    mat = val
                    break

            # Parsuj rozmery
            geo = parse_dimensions(dim_str, mat)
            t   = geo["thickness_mm"]

            # Zostav parametre
            params = {
                "material":          mat,
                "thickness_mm":      t,
                "quantity":          qty,
                "hourly_rate":       float(default_params.get("hourly_rate", 80)),
                "setup_time_min":    float(default_params.get("setup_time_min", 10)),
                "margin_pct":        float(default_params.get("margin_pct", 20)),
                "material_margin_pct": float(default_params.get("material_margin_pct", 20)),
                "scrap_factor":      float(default_params.get("scrap_factor", 1.25)),
                "shape_factor":      1.0,
                "holes":             [],
                "powder_coating":    False,
            }

            result = calculate_price(geo, params)
            results.append({
                "pos":           p.get("pos"),
                "ok":            True,
                "material":      mat,
                "thickness_mm":  t,
                "dimensions":    dim_str,
                "result":        result,
            })
        except Exception as e:
            results.append({"pos": p.get("pos"), "ok": False, "error": str(e)})

    return jsonify({"ok": True, "results": results})


@app.route('/calculate', methods=['POST'])
def calculate():
    data = request.get_json()
    geometry = data.get("geometry")
    params = data.get("params")

    if not geometry or not params:
        return jsonify({"error": "Chýbajú dáta"}), 400

    try:
        result = calculate_price(geometry, params)
        return jsonify({"ok": True, "result": result})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route('/calculate-bending', methods=['POST'])
def calculate_bending():
    """Vypočíta cenu ohýbania na základe zoznamu ohybov a parametrov."""
    data = request.get_json()
    bends = data.get("bends", [])
    qty = int(data.get("qty", 1))
    margin_pct = float(data.get("margin_pct", 20.0))
    weight_kg = float(data.get("weight_kg", 0.0))

    try:
        result = calculate_bending_price(bends, qty, margin_pct, weight_kg)
        return jsonify({"ok": True, "result": result})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route('/calculate-rolling', methods=['POST'])
def calculate_rolling():
    """Vypočíta cenu valcovania."""
    data = request.get_json()
    rolls        = data.get("rolls", [])
    thickness_mm = float(data.get("thickness_mm", 3))
    qty          = int(data.get("qty", 1))
    margin_pct   = float(data.get("margin_pct", 20.0))
    try:
        result = calculate_rolling_price(rolls, thickness_mm, qty, margin_pct)
        return jsonify({"ok": True, "result": result})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route('/generate-bom-quote', methods=['POST'])
def generate_bom_quote():
    """PDF cenová ponuka pre zostavu (BOM) — štýl Flowii/TecKon."""
    import datetime, time as _time
    data         = request.get_json()
    bom          = data.get("bom", {})
    items        = data.get("items", [])   # [{pos, name, qty, price_per_piece, total, type}, ...]
    company      = data.get("company", {})
    quote_number = data.get("quote_number", "") or f"CP-{str(int(_time.time()))[-6:]}"
    lang         = data.get("lang", "de")
    vat_pct      = int(data.get("vat_pct", 0))
    series_qty   = int(data.get("series_qty", 1))

    T = {
        "de": {"title":"Preisangebot","customer_label":"Abnehmer:","date_label":"Ausgestellt am:",
               "valid_label":"Gültig bis:","nr":"Nr.","artikel":"Artikel","menge":"Menge","me":"ME",
               "vat_pct":"MwSt. (%)","unit_price":"Einheitspreis","total_col":"Insgesamt",
               "total_excl":"Gesamtbetrag exkl. MwSt.","total_incl":"Gesamtbetrag inkl. MwSt.",
               "conditions":"Lieferfrist - 4 Wochen\nAlle Preise sind EXW SK-Bytča\nZahlungsbedingungen - 30 Tage netto",
               "issued_by":"Ausgestellt von:","accepted_by":"Abnahme durch:"},
        "sk": {"title":"Cenová ponuka","customer_label":"Zákazník:","date_label":"Dátum:",
               "valid_label":"Platná do:","nr":"č.","artikel":"Položka","menge":"Množstvo","me":"MJ",
               "vat_pct":"DPH (%)","unit_price":"Jedn. cena bez DPH","total_col":"Celkom bez DPH",
               "total_excl":"Celková suma bez DPH","total_incl":"Celková suma vrát. DPH",
               "conditions":"Dodacia lehota - 4 týždne\nVšetky ceny sú EXW SK-Bytča\nSplatnosť - 30 dní netto",
               "issued_by":"Vystavil:","accepted_by":"Prevzal:"},
    }.get(lang, {})

    ORANGE=colors.HexColor('#f97316'); ORANGE_BG=colors.HexColor('#fff7ed')
    DARK=colors.HexColor('#1c1917'); MUTED=colors.HexColor('#78716c')
    LIGHT=colors.HexColor('#fafaf9'); BORDER=colors.HexColor('#e7e5e4')

    buf = BytesIO()
    doc = SimpleDocTemplate(buf, pagesize=A4,
        leftMargin=18*mm, rightMargin=18*mm, topMargin=15*mm, bottomMargin=20*mm)

    def sty(name, **kw):
        return ParagraphStyle(name, parent=getSampleStyleSheet()['Normal'], **kw)

    s_normal = sty('N', fontSize=9, fontName=_PDF_FONT, textColor=DARK, leading=13)
    s_small  = sty('S', fontSize=8, fontName=_PDF_FONT, textColor=MUTED, leading=11)
    s_bold   = sty('B', fontSize=9, fontName=_PDF_FONT_BOLD, textColor=DARK, leading=13)
    s_right  = sty('R', fontSize=9, fontName=_PDF_FONT, textColor=DARK, alignment=TA_RIGHT, leading=13)
    s_title  = sty('TT',fontSize=16, fontName=_PDF_FONT_BOLD, textColor=DARK, alignment=TA_RIGHT, leading=20)

    def eur(v):
        try: return f'{float(v):,.2f}'.replace(',','X').replace('.', ',').replace('X','.') + ' €'
        except: return '0,00 €'

    story = []
    today    = datetime.date.today()
    valid_dt = today + datetime.timedelta(days=30)

    # ── HLAVIČKA ─────────────────────────────────────────────────────
    logo_path = os.path.join(os.path.dirname(__file__), 'logo.jpeg')
    logo_cell = RLImage(logo_path, width=42*mm, height=16*mm, kind='proportional') \
                if os.path.exists(logo_path) else Paragraph('<b>TecKon s.r.o.</b>', s_bold)

    hdr = Table([[logo_cell,
        Paragraph(f'{T["title"]}: <b>{quote_number}</b>', s_title),
    ]], colWidths=[80*mm, 92*mm])
    hdr.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'MIDDLE'),
        ('LINEBELOW',(0,0),(-1,0),0.5,BORDER),('BOTTOMPADDING',(0,0),(-1,0),6)]))
    story.append(hdr)
    story.append(Spacer(1,5*mm))

    # ── ADRESY ───────────────────────────────────────────────────────
    cust_name = company.get("name","")
    cust_addr = company.get("address","")
    cust_uid  = company.get("uid","")
    teckon_txt = ('<b>TecKon s.r.o.</b><br/>Malobytčianska cesta 1486<br/>014 01 Bytča<br/>'
                  'the Slovak Republic<br/><br/>ID-Nr.:&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;47183179<br/>'
                  'Steuer-ID-Nr.:&nbsp;2023819721<br/>UID:&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;SK2023819721')
    cust_box = Table([[Paragraph(f'<b>{cust_name}</b><br/><br/>{cust_addr}', s_normal)]],
                     colWidths=[85*mm])
    cust_box.setStyle(TableStyle([('BOX',(0,0),(-1,-1),0.8,BORDER),
        ('PADDING',(0,0),(-1,-1),8),('BACKGROUND',(0,0),(-1,-1),LIGHT)]))
    addr = Table([[Paragraph(teckon_txt, s_small),
        Table([[Paragraph(T["customer_label"], s_small)],[cust_box],
               [Paragraph(f'UID: {cust_uid}' if cust_uid else '', s_small)],
               [Spacer(1,2*mm)],
               [Paragraph(f'{T["date_label"]} {today.strftime("%d.%m.%Y")}', s_small)],
               [Paragraph(f'{T["valid_label"]} {valid_dt.strftime("%d.%m.%Y")}', s_small)],
               ], colWidths=[92*mm])
    ]], colWidths=[75*mm, 97*mm])
    addr.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'TOP')]))
    story.append(addr)
    story.append(Spacer(1,5*mm))

    # Zostava info
    asm_name = bom.get("assembly_name","Zostava")
    asm_nr   = bom.get("drawing_number","")
    story.append(Paragraph(f'{asm_name}  {asm_nr}  —  {series_qty} ks', s_small))
    story.append(Spacer(1,3*mm))

    # ── TABUĽKA POLOŽIEK ─────────────────────────────────────────────
    col_w = [10*mm, 75*mm, 18*mm, 10*mm, 13*mm, 28*mm, 18*mm]
    rows = [[
        Paragraph(T["nr"],        sty('th',  fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white)),
        Paragraph(T["artikel"],   sty('th2', fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white)),
        Paragraph(T["menge"],     sty('th3', fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white, alignment=TA_RIGHT)),
        Paragraph(T["me"],        sty('th4', fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white, alignment=TA_RIGHT)),
        Paragraph(T["vat_pct"],   sty('th5', fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white, alignment=TA_RIGHT)),
        Paragraph(T["unit_price"],sty('th6', fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white, alignment=TA_RIGHT)),
        Paragraph(T["total_col"], sty('th7', fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white, alignment=TA_RIGHT)),
    ]]

    grand_excl = 0.0
    for item in items:
        price = float(item.get("price_per_piece", 0))
        qty   = int(item.get("qty", 1))
        total = float(item.get("total", price * qty))
        grand_excl += total
        type_note = ' 🛒' if item.get("type") == "bought" else ''
        rows.append([
            Paragraph(str(item.get("pos","")), sty('r1', fontSize=8, fontName=_PDF_FONT, textColor=DARK)),
            Paragraph(f'{item.get("name","")}{type_note}',
                      sty('r2', fontSize=8, fontName=_PDF_FONT, textColor=DARK)),
            Paragraph(str(qty), sty('r3', fontSize=8, fontName=_PDF_FONT, textColor=DARK, alignment=TA_RIGHT)),
            Paragraph('Stk',   sty('r4', fontSize=8, fontName=_PDF_FONT, textColor=DARK, alignment=TA_RIGHT)),
            Paragraph(str(vat_pct), sty('r5', fontSize=8, fontName=_PDF_FONT, textColor=DARK, alignment=TA_RIGHT)),
            Paragraph(eur(price), sty('r6', fontSize=8, fontName=_PDF_FONT, textColor=DARK, alignment=TA_RIGHT)),
            Paragraph(eur(total), sty('r7', fontSize=8, fontName=_PDF_FONT, textColor=DARK, alignment=TA_RIGHT)),
        ])

    tbl = Table(rows, colWidths=col_w, repeatRows=1)
    tbl.setStyle(TableStyle([
        ('BACKGROUND',(0,0),(-1,0),ORANGE),
        ('ROWBACKGROUNDS',(0,1),(-1,-1),[colors.white, LIGHT]),
        ('GRID',(0,0),(-1,-1),0.3,BORDER),
        ('VALIGN',(0,0),(-1,-1),'TOP'),
        ('TOPPADDING',(0,0),(-1,-1),4),('BOTTOMPADDING',(0,0),(-1,-1),4),
        ('LEFTPADDING',(0,0),(-1,-1),4),
    ]))
    story.append(tbl)
    story.append(Spacer(1,4*mm))

    # ── SUMY ─────────────────────────────────────────────────────────
    grand_incl = grand_excl * (1 + vat_pct/100)
    sum_rows = [
        [Paragraph(T["total_excl"], sty('sl', fontSize=9, fontName=_PDF_FONT, textColor=DARK, alignment=TA_RIGHT)),
         Paragraph(eur(grand_excl), sty('sv', fontSize=9, fontName=_PDF_FONT, textColor=DARK, alignment=TA_RIGHT))],
    ]
    if vat_pct > 0:
        sum_rows.append([
            Paragraph(f'MwSt. {vat_pct}%', sty('sl2', fontSize=9, fontName=_PDF_FONT, textColor=DARK, alignment=TA_RIGHT)),
            Paragraph(eur(grand_incl-grand_excl), sty('sv2', fontSize=9, fontName=_PDF_FONT, textColor=DARK, alignment=TA_RIGHT)),
        ])
    sum_rows.append([
        Paragraph(f'<b>{T["total_incl"]}</b>', sty('sl3', fontSize=10, fontName=_PDF_FONT_BOLD, textColor=DARK, alignment=TA_RIGHT)),
        Paragraph(f'<b>{eur(grand_incl)}</b>', sty('sv3', fontSize=10, fontName=_PDF_FONT_BOLD, textColor=DARK, alignment=TA_RIGHT)),
    ])
    sum_tbl = Table(sum_rows, colWidths=[130*mm, 42*mm])
    sum_tbl.setStyle(TableStyle([
        ('BACKGROUND',(0,len(sum_rows)-1),(-1,len(sum_rows)-1),ORANGE_BG),
        ('LINEABOVE',(0,len(sum_rows)-1),(-1,len(sum_rows)-1),1,ORANGE),
        ('TOPPADDING',(0,0),(-1,-1),4),('BOTTOMPADDING',(0,0),(-1,-1),4),
        ('RIGHTPADDING',(0,0),(-1,-1),4),
    ]))
    story.append(sum_tbl)
    story.append(Spacer(1,6*mm))

    # ── PODMIENKY + PODPISY ───────────────────────────────────────────
    for line in T.get("conditions","").split('\n'):
        story.append(Paragraph(line, s_small))
    story.append(Spacer(1,10*mm))
    sig = Table([[
        Paragraph(f'<b>{T["issued_by"]}</b><br/><br/>Michal Lukačko<br/>michal.lukacko@teckon.sk<br/>0910 216 123', s_small),
        Paragraph(f'<b>{T["accepted_by"]}</b>', s_small),
    ]], colWidths=[85*mm, 87*mm])
    sig.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'TOP')]))
    story.append(sig)

    doc.build(story)
    pdf_bytes = buf.getvalue()
    response = make_response(pdf_bytes)
    response.headers['Content-Type'] = 'application/pdf'
    response.headers['Content-Disposition'] = f'attachment; filename="Preisangebot_{quote_number}.pdf"'
    return response


@app.route('/generate-multiqty-quote', methods=['POST'])
def generate_multiqty_quote():
    """PDF s cenovými hladinami pre rôzne množstvá."""
    import datetime, time as _time
    data         = request.get_json()
    rows         = data.get("rows", [])
    part_desc    = data.get("part_description", "Výpalok")
    material     = data.get("material", "")
    thickness    = data.get("thickness_mm", "")
    quote_number = data.get("quote_number", "") or f"CP-{str(int(_time.time()))[-6:]}"
    lang         = data.get("lang", "de")
    company      = data.get("company", {})

    ORANGE=colors.HexColor('#f97316'); ORANGE_BG=colors.HexColor('#fff7ed')
    DARK=colors.HexColor('#1c1917'); MUTED=colors.HexColor('#78716c')
    LIGHT=colors.HexColor('#fafaf9'); BORDER=colors.HexColor('#e7e5e4')
    GREEN=colors.HexColor('#16a34a')

    buf = BytesIO()
    doc = SimpleDocTemplate(buf, pagesize=A4,
        leftMargin=18*mm, rightMargin=18*mm, topMargin=15*mm, bottomMargin=20*mm)

    def sty(name, **kw):
        return ParagraphStyle(name, parent=getSampleStyleSheet()['Normal'], **kw)

    s_normal = sty('N', fontSize=9, fontName=_PDF_FONT, textColor=DARK, leading=13)
    s_small  = sty('S', fontSize=8, fontName=_PDF_FONT, textColor=MUTED, leading=11)
    s_bold   = sty('B', fontSize=9, fontName=_PDF_FONT_BOLD, textColor=DARK, leading=13)
    s_right  = sty('R', fontSize=9, fontName=_PDF_FONT, textColor=DARK, alignment=TA_RIGHT)
    s_title  = sty('TT',fontSize=16, fontName=_PDF_FONT_BOLD, textColor=DARK, alignment=TA_RIGHT, leading=20)

    def eur(v):
        try: return f'{float(v):,.2f}'.replace(',','X').replace('.', ',').replace('X','.') + ' €'
        except: return '0,00 €'

    today    = datetime.date.today()
    valid_dt = today + datetime.timedelta(days=30)
    title_label = "Preisangebot" if lang == "de" else "Cenová ponuka"

    story = []

    # Hlavička
    logo_path = os.path.join(os.path.dirname(__file__), 'logo.jpeg')
    logo_cell = RLImage(logo_path, width=42*mm, height=16*mm, kind='proportional') \
                if os.path.exists(logo_path) else Paragraph('<b>TecKon s.r.o.</b>', s_bold)

    hdr = Table([[logo_cell,
        Paragraph(f'{title_label}: <b>{quote_number}</b>', s_title),
    ]], colWidths=[80*mm, 92*mm])
    hdr.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'MIDDLE'),
        ('LINEBELOW',(0,0),(-1,0),0.5,BORDER),('BOTTOMPADDING',(0,0),(-1,0),6)]))
    story.append(hdr)
    story.append(Spacer(1,5*mm))

    # Adresy
    cust_name = company.get("name","")
    cust_addr = company.get("address","")
    cust_uid  = company.get("uid","")
    teckon_txt = ('<b>TecKon s.r.o.</b><br/>Malobytčianska cesta 1486<br/>014 01 Bytča<br/>'
                  'the Slovak Republic<br/><br/>ID-Nr.: 47183179<br/>UID: SK2023819721')
    cust_box = Table([[Paragraph(f'<b>{cust_name}</b><br/><br/>{cust_addr}', s_normal)]],
                     colWidths=[85*mm])
    cust_box.setStyle(TableStyle([('BOX',(0,0),(-1,-1),0.8,BORDER),
        ('PADDING',(0,0),(-1,-1),8),('BACKGROUND',(0,0),(-1,-1),LIGHT)]))
    addr = Table([[Paragraph(teckon_txt, s_small),
        Table([[Paragraph('Abnehmer:' if lang=='de' else 'Zákazník:', s_small)],
               [cust_box],[Paragraph(f'UID: {cust_uid}' if cust_uid else '', s_small)],
               [Spacer(1,2*mm)],
               [Paragraph(f'{"Ausgestellt am" if lang=="de" else "Dátum"}: {today.strftime("%d.%m.%Y")}', s_small)],
               [Paragraph(f'{"Gültig bis" if lang=="de" else "Platná do"}: {valid_dt.strftime("%d.%m.%Y")}', s_small)],
               ], colWidths=[92*mm])
    ]], colWidths=[75*mm, 97*mm])
    addr.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'TOP')]))
    story.append(addr)
    story.append(Spacer(1,5*mm))

    # Diel info
    story.append(Paragraph(f'{part_desc} · {material.upper()} {thickness}mm', s_small))
    story.append(Spacer(1,4*mm))

    # Tabuľka cenových hladín
    col_w = [25*mm, 35*mm, 35*mm, 30*mm, 30*mm, 17*mm]
    menge_lbl = "Menge" if lang == "de" else "Množstvo"
    rows_tbl = [[
        Paragraph(menge_lbl, sty('th1', fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white)),
        Paragraph("Einheitspreis" if lang=="de" else "Cena / ks",
                  sty('th2', fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white, alignment=TA_RIGHT)),
        Paragraph("Gesamtbetrag" if lang=="de" else "Celkom",
                  sty('th3', fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white, alignment=TA_RIGHT)),
        Paragraph("Material / Stk" if lang=="de" else "Materiál / ks",
                  sty('th4', fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white, alignment=TA_RIGHT)),
        Paragraph("Maschine / Stk" if lang=="de" else "Stroj / ks",
                  sty('th5', fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white, alignment=TA_RIGHT)),
        Paragraph("Marge" if lang=="de" else "Zisk",
                  sty('th6', fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white, alignment=TA_RIGHT)),
    ]]

    min_price = min((float(r.get("price_per_piece",0)) for r in rows), default=0)
    for i, row in enumerate(rows):
        ppp   = float(row.get("price_per_piece", 0))
        total = float(row.get("price_total", 0))
        mat   = float(row.get("material_cost_sell", 0))
        mach  = float(row.get("machine_cost_per_piece", 0))
        cost  = float(row.get("cost_per_piece", 0))
        profit_pct = round((ppp - cost) / cost * 100) if cost > 0 else 0
        is_best = abs(ppp - min_price) < 0.001
        bg = colors.HexColor('#f0fdf4') if is_best else (LIGHT if i%2==0 else colors.white)
        best_star = ' ★' if is_best else ''

        rows_tbl.append([
            Paragraph(f'{row.get("qty","")} Stk{best_star}',
                      sty(f'r1_{i}', fontSize=9, fontName=_PDF_FONT_BOLD if is_best else _PDF_FONT,
                          textColor=GREEN if is_best else DARK)),
            Paragraph(eur(ppp),
                      sty(f'r2_{i}', fontSize=9, fontName=_PDF_FONT_BOLD if is_best else _PDF_FONT,
                          textColor=GREEN if is_best else DARK, alignment=TA_RIGHT)),
            Paragraph(eur(total),
                      sty(f'r3_{i}', fontSize=9, fontName=_PDF_FONT, textColor=DARK, alignment=TA_RIGHT)),
            Paragraph(eur(mat),
                      sty(f'r4_{i}', fontSize=8, fontName=_PDF_FONT, textColor=MUTED, alignment=TA_RIGHT)),
            Paragraph(eur(mach),
                      sty(f'r5_{i}', fontSize=8, fontName=_PDF_FONT, textColor=MUTED, alignment=TA_RIGHT)),
            Paragraph(f'{profit_pct}%',
                      sty(f'r6_{i}', fontSize=8, fontName=_PDF_FONT, textColor=GREEN, alignment=TA_RIGHT)),
        ])

    tbl = Table(rows_tbl, colWidths=col_w, repeatRows=1)
    tbl.setStyle(TableStyle([
        ('BACKGROUND',(0,0),(-1,0), ORANGE),
        ('GRID',(0,0),(-1,-1),0.3,BORDER),
        ('VALIGN',(0,0),(-1,-1),'MIDDLE'),
        ('TOPPADDING',(0,0),(-1,-1),5),('BOTTOMPADDING',(0,0),(-1,-1),5),
        ('LEFTPADDING',(0,0),(-1,-1),5),
    ]))
    # Zelené pozadie pre najlepšiu cenu
    for i, row in enumerate(rows):
        ppp = float(row.get("price_per_piece",0))
        if abs(ppp - min_price) < 0.001:
            tbl.setStyle(TableStyle([('BACKGROUND',(0,i+1),(-1,i+1), colors.HexColor('#f0fdf4'))]))

    story.append(tbl)
    story.append(Spacer(1,6*mm))

    # Podmienky
    conds = ("Lieferfrist - 4 Wochen\nAlle Preise sind EXW SK-Bytča\nZahlungsbedingungen - 30 Tage netto"
             if lang == "de" else
             "Dodacia lehota - 4 týždne\nVšetky ceny sú EXW SK-Bytča\nSplatnosť - 30 dní netto")
    for line in conds.split('\n'):
        story.append(Paragraph(line, s_small))
    story.append(Spacer(1,10*mm))

    sig = Table([[
        Paragraph(f'<b>{"Ausgestellt von" if lang=="de" else "Vystavil"}:</b><br/><br/>'
                  'Michal Lukačko<br/>michal.lukacko@teckon.sk<br/>0910 216 123', s_small),
        Paragraph(f'<b>{"Abnahme durch" if lang=="de" else "Prevzal"}:</b>', s_small),
    ]], colWidths=[85*mm, 87*mm])
    sig.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'TOP')]))
    story.append(sig)

    doc.build(story)
    pdf_bytes = buf.getvalue()
    response = make_response(pdf_bytes)
    response.headers['Content-Type'] = 'application/pdf'
    response.headers['Content-Disposition'] = f'attachment; filename="Preisangebot_{quote_number}_Mengen.pdf"'
    return response


@app.route('/generate-quote', methods=['POST'])
def generate_quote():
    """Vygeneruje cenovú ponuku ako PDF — štýl Flowii/TecKon."""
    import datetime
    import time as _time
    data = request.get_json()
    r        = data.get("result", {})
    params   = data.get("params", {})
    bending  = data.get("bending", {})
    rolling  = data.get("rolling", {})
    company  = data.get("company", {})
    part_desc   = data.get("part_description", "Výpalok")
    quote_number = data.get("quote_number", "") or f"CP-{str(int(_time.time()))[-6:]}"
    lang     = data.get("lang", "de")  # "de" alebo "sk"

    # ── Texty podľa jazyka (de/sk) ────────────────────────────────────
    T = {
        "de": {
            "title": "Preisangebot",
            "customer_label": "Abnehmer:",
            "date_label": "Ausgestellt am:",
            "valid_label": "Gültig bis:",
            "nr": "Nr.", "artikel": "Artikel", "menge": "Menge", "me": "ME",
            "vat_pct": "MwSt. (%)", "unit_price": "Einheitspreis zzgl. MwSt.",
            "total_col": "Insgesamt zzgl. MwSt.",
            "total_excl": "Gesamtbetrag exkl. MwSt.",
            "total_incl": "Gesamtbetrag inkl. MwSt.",
            "laser": "Laserschneiden", "material": "Material",
            "bending": "Biegen", "powder": "Pulverbeschichtung", "drilling": "Bohren", "rolling": "Walzen",
            "conditions": "Lieferfrist - 4 Wochen\nAlle Preise sind EXW SK-Bytča\nZahlungsbedingungen - 30 Tage netto",
            "issued_by": "Ausgestellt von:", "accepted_by": "Abnahme durch:",
        },
        "sk": {
            "title": "Cenová ponuka",
            "customer_label": "Zákazník:",
            "date_label": "Dátum:",
            "valid_label": "Platná do:",
            "nr": "č.", "artikel": "Položka", "menge": "Množstvo", "me": "MJ",
            "vat_pct": "DPH (%)", "unit_price": "Jedn. cena bez DPH",
            "total_col": "Celkom bez DPH",
            "total_excl": "Celková suma bez DPH",
            "total_incl": "Celková suma vrát. DPH",
            "laser": "Laserové rezanie", "material": "Materiál",
            "bending": "Ohýbanie", "powder": "Prášková farba", "drilling": "Vŕtanie", "rolling": "Valcovanie",
            "conditions": "Dodacia lehota - 4 týždne\nVšetky ceny sú EXW SK-Bytča\nSplatnosť - 30 dní netto",
            "issued_by": "Vystavil:", "accepted_by": "Prevzal:",
        },
    }.get(lang, {})
    if not T: T = {
        "title":"Preisangebot","customer_label":"Abnehmer:","date_label":"Ausgestellt am:",
        "valid_label":"Gültig bis:","nr":"Nr.","artikel":"Artikel","menge":"Menge","me":"ME",
        "vat_pct":"MwSt. (%)","unit_price":"Einheitspreis zzgl. MwSt.","total_col":"Insgesamt zzgl. MwSt.",
        "total_excl":"Gesamtbetrag exkl. MwSt.","total_incl":"Gesamtbetrag inkl. MwSt.",
        "laser":"Laserschneiden","material":"Material","bending":"Biegen",
        "powder":"Pulverbeschichtung","drilling":"Bohren","rolling":"Walzen",
        "conditions":"Lieferfrist - 4 Wochen\nAlle Preise sind EXW SK-Bytča\nZahlungsbedingungen - 30 Tage netto",
        "issued_by":"Ausgestellt von:","accepted_by":"Abnahme durch:",
    }

    # ── Farby TecKon ──────────────────────────────────────────────────
    ORANGE    = colors.HexColor('#f97316')
    ORANGE_BG = colors.HexColor('#fff7ed')
    DARK      = colors.HexColor('#1c1917')
    MUTED     = colors.HexColor('#78716c')
    LIGHT     = colors.HexColor('#fafaf9')
    BORDER    = colors.HexColor('#e7e5e4')

    buf = BytesIO()
    doc = SimpleDocTemplate(buf, pagesize=A4,
        leftMargin=18*mm, rightMargin=18*mm,
        topMargin=15*mm, bottomMargin=20*mm)

    def sty(name, **kw):
        return ParagraphStyle(name, parent=getSampleStyleSheet()['Normal'], **kw)

    s_normal = sty('N',  fontSize=9,  fontName=_PDF_FONT,      textColor=DARK,   leading=13)
    s_small  = sty('S',  fontSize=8,  fontName=_PDF_FONT,      textColor=MUTED,  leading=11)
    s_bold   = sty('B',  fontSize=9,  fontName=_PDF_FONT_BOLD, textColor=DARK,   leading=13)
    s_right  = sty('R',  fontSize=9,  fontName=_PDF_FONT,      textColor=DARK,   alignment=TA_RIGHT, leading=13)
    s_title  = sty('TT', fontSize=16, fontName=_PDF_FONT_BOLD, textColor=DARK,   alignment=TA_RIGHT, leading=20)
    s_orange = sty('O',  fontSize=9,  fontName=_PDF_FONT_BOLD, textColor=ORANGE, alignment=TA_RIGHT)

    def eur(v):
        try:    return f'{float(v):,.2f}'.replace(',', 'X').replace('.', ',').replace('X', '.') + ' €'
        except: return '0,00 €'

    qty      = int(params.get("quantity", 1))
    today    = datetime.date.today()
    valid_dt = today + datetime.timedelta(days=30)
    vat_pct  = int(data.get("vat_pct", 0))

    story = []

    # ── 1. HLAVIČKA: logo + názov ─────────────────────────────────────
    logo_path = os.path.join(os.path.dirname(__file__), 'logo.jpeg')
    logo_cell = RLImage(logo_path, width=42*mm, height=16*mm, kind='proportional') \
                if os.path.exists(logo_path) \
                else Paragraph('<b>TecKon s.r.o.</b>', s_bold)

    hdr = Table([[
        logo_cell,
        Paragraph(f'{T["title"]}: <b>{quote_number}</b>', s_title),
    ]], colWidths=[80*mm, 92*mm])
    hdr.setStyle(TableStyle([
        ('VALIGN', (0,0), (-1,-1), 'MIDDLE'),
        ('LINEBELOW', (0,0), (-1,0), 0.5, BORDER),
        ('BOTTOMPADDING', (0,0), (-1,0), 6),
    ]))
    story.append(hdr)
    story.append(Spacer(1, 5*mm))

    # ── 2. ADRESA: TecKon vlavo, zákazník vpravo ──────────────────────
    cust_name = company.get("name","")
    cust_addr = company.get("address","")
    cust_uid  = company.get("uid","")

    teckon_txt = (
        '<b>TecKon s.r.o.</b><br/>'
        'Malobytčianska cesta 1486<br/>014 01 Bytča<br/>the Slovak Republic<br/><br/>'
        'ID-Nr.:&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;47183179<br/>'
        'Steuer-ID-Nr.:&nbsp;2023819721<br/>'
        'UID:&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;SK2023819721<br/>'
        'Okr. súd Žilina, odd. Sro, vl. č. 59322/L'
    )

    cust_box_content = (
        f'<b>{cust_name}</b><br/><br/>'
        f'{cust_addr.replace(chr(10), "<br/>")}'
    )
    cust_box = Table([[Paragraph(cust_box_content, s_normal)]],
                     colWidths=[85*mm])
    cust_box.setStyle(TableStyle([
        ('BOX', (0,0), (-1,-1), 0.8, BORDER),
        ('PADDING', (0,0), (-1,-1), 8),
        ('BACKGROUND', (0,0), (-1,-1), LIGHT),
    ]))

    addr_section = Table([[
        Paragraph(teckon_txt, s_small),
        Table([
            [Paragraph(T["customer_label"], s_small)],
            [cust_box],
            [Paragraph(f'UID: {cust_uid}' if cust_uid else '', s_small)],
            [Spacer(1,2*mm)],
            [Paragraph(f'{T["date_label"]} {today.strftime("%d.%m.%Y")}', s_small)],
            [Paragraph(f'{T["valid_label"]} {valid_dt.strftime("%d.%m.%Y")}', s_small)],
        ], colWidths=[92*mm]),
    ]], colWidths=[75*mm, 97*mm])
    addr_section.setStyle(TableStyle([
        ('VALIGN', (0,0), (-1,-1), 'TOP'),
    ]))
    story.append(addr_section)
    story.append(Spacer(1, 5*mm))

    # Referencia zákazníka
    ref = data.get("customer_reference","")
    if ref:
        story.append(Paragraph(ref, s_small))
        story.append(Spacer(1, 3*mm))

    # ── 3. TABUĽKA POLOŽIEK ───────────────────────────────────────────
    laser_total  = float(r.get("price_total", 0))
    bend_total   = float(bending.get("bending_total", 0)) if bending else 0.0
    roll_total   = float(rolling.get("rolling_total", 0)) if rolling else 0.0
    grand_excl   = laser_total + bend_total + roll_total
    grand_incl  = grand_excl * (1 + vat_pct / 100)

    # Hlavička tabuľky
    rows = [[
        Paragraph(T["nr"],        sty('th', fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white)),
        Paragraph(T["artikel"],   sty('th2', fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white)),
        Paragraph(T["menge"],     sty('th3', fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white, alignment=TA_RIGHT)),
        Paragraph(T["me"],        sty('th4', fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white, alignment=TA_RIGHT)),
        Paragraph(T["vat_pct"],   sty('th5', fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white, alignment=TA_RIGHT)),
        Paragraph(T["unit_price"],sty('th6', fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white, alignment=TA_RIGHT)),
        Paragraph(T["total_col"], sty('th7', fontSize=8, fontName=_PDF_FONT_BOLD, textColor=colors.white, alignment=TA_RIGHT)),
    ]]

    def make_row(nr, name, sub, qty_val, me, vat, unit, total):
        return [
            Paragraph(str(nr), s_small),
            Paragraph(f'<b>{name}</b><br/><font size="7" color="#78716c">{sub}</font>', s_normal),
            Paragraph(str(qty_val), sty('rv', fontSize=9, textColor=DARK, alignment=TA_RIGHT)),
            Paragraph(me,  sty('rv2', fontSize=9, textColor=DARK, alignment=TA_RIGHT)),
            Paragraph(str(vat), sty('rv3', fontSize=9, textColor=DARK, alignment=TA_RIGHT)),
            Paragraph(eur(unit), sty('rv4', fontSize=9, textColor=DARK, alignment=TA_RIGHT)),
            Paragraph(eur(total), sty('rv5', fontSize=9, textColor=DARK, alignment=TA_RIGHT)),
        ]

    nr = 1
    mat_str = f'{params.get("material","").upper()} {params.get("thickness_mm","")}mm'

    # Rezanie + materiál (ako 1 položka — predajná cena/ks)
    rows.append(make_row(nr, part_desc, mat_str,
        qty, 'Stk', vat_pct,
        r.get("price_per_piece", 0),
        laser_total))
    nr += 1

    # Ohýbanie
    if bending and bending.get("bending_applicable"):
        rows.append(make_row(nr, T["bending"],
            f'{bending.get("bend_count",0)} Biegungen',
            qty, 'Stk', vat_pct,
            bending.get("bending_sell_per_piece", 0),
            bending.get("bending_total", 0)))
        nr += 1

    # Valcovanie
    if rolling and rolling.get("rolling_applicable"):
        rows.append(make_row(nr, T.get("rolling", "Walzen / Valcovanie"),
            f'{rolling.get("roll_count",0)} Bögen · {rolling.get("unique_radii",0)}× Setup · {rolling.get("total_length_m",0)} m',
            qty, 'Stk', vat_pct,
            rolling.get("rolling_sell_per_piece", 0),
            rolling.get("rolling_total", 0)))
        nr += 1

    # Prášková farba
    if r.get("powder_coating"):
        rows.append(make_row(nr, T["powder"],
            f'{r.get("powder_area_per_piece_m2",0):.3f} m² · {r.get("powder_oven_cycles",0)} Takt(e)',
            qty, 'Stk', vat_pct,
            r.get("powder_cost_per_piece", 0),
            float(r.get("powder_cost_per_piece", 0)) * qty))
        nr += 1

    # Vŕtanie
    if r.get("drill_cost", 0) > 0:
        rows.append(make_row(nr, T["drilling"], '',
            qty, 'Stk', vat_pct,
            r.get("drill_cost", 0),
            float(r.get("drill_cost", 0)) * qty))
        nr += 1

    col_w = [10*mm, 65*mm, 18*mm, 10*mm, 13*mm, 28*mm, 28*mm]
    tbl = Table(rows, colWidths=col_w, repeatRows=1)
    n_data = len(rows)
    tbl.setStyle(TableStyle([
        ('BACKGROUND',   (0,0), (-1,0), ORANGE),
        ('ROWBACKGROUNDS',(0,1), (-1,-1), [colors.white, LIGHT]),
        ('GRID',         (0,0), (-1,-1), 0.3, BORDER),
        ('FONTSIZE',     (0,1), (-1,-1), 8),
        ('VALIGN',       (0,0), (-1,-1), 'TOP'),
        ('TOPPADDING',   (0,0), (-1,-1), 4),
        ('BOTTOMPADDING',(0,0), (-1,-1), 4),
        ('LEFTPADDING',  (0,0), (-1,-1), 4),
    ]))
    story.append(tbl)
    story.append(Spacer(1, 4*mm))

    # ── 4. SUMY ───────────────────────────────────────────────────────
    sum_rows = [
        [Paragraph(T["total_excl"], sty('sl', fontSize=9, textColor=DARK, alignment=TA_RIGHT)),
         Paragraph(eur(grand_excl), sty('sv', fontSize=9, textColor=DARK, alignment=TA_RIGHT))],
    ]
    if vat_pct > 0:
        sum_rows.append([
            Paragraph(f'MwSt. {vat_pct}%', sty('sl2', fontSize=9, textColor=DARK, alignment=TA_RIGHT)),
            Paragraph(eur(grand_incl - grand_excl), sty('sv2', fontSize=9, textColor=DARK, alignment=TA_RIGHT)),
        ])
    sum_rows.append([
        Paragraph(f'<b>{T["total_incl"]}</b>', sty('sl3', fontSize=10, fontName=_PDF_FONT_BOLD, textColor=DARK, alignment=TA_RIGHT)),
        Paragraph(f'<b>{eur(grand_incl)}</b>', sty('sv3', fontSize=10, fontName=_PDF_FONT_BOLD, textColor=DARK, alignment=TA_RIGHT)),
    ])

    sum_tbl = Table(sum_rows, colWidths=[130*mm, 42*mm])
    sum_tbl.setStyle(TableStyle([
        ('BACKGROUND', (0, len(sum_rows)-1), (-1, len(sum_rows)-1), ORANGE_BG),
        ('LINEABOVE',  (0, len(sum_rows)-1), (-1, len(sum_rows)-1), 1, ORANGE),
        ('TOPPADDING',    (0,0), (-1,-1), 4),
        ('BOTTOMPADDING', (0,0), (-1,-1), 4),
        ('RIGHTPADDING',  (0,0), (-1,-1), 4),
    ]))
    story.append(sum_tbl)
    story.append(Spacer(1, 6*mm))

    # ── 5. PODMIENKY ──────────────────────────────────────────────────
    conditions = data.get("conditions", T["conditions"])
    for line in conditions.split('\n'):
        story.append(Paragraph(line, s_small))
    story.append(Spacer(1, 10*mm))

    # ── 6. PODPISY ────────────────────────────────────────────────────
    sig_tbl = Table([[
        Paragraph(f'<b>{T["issued_by"]}</b><br/><br/>'
                  'Michal Lukačko<br/>michal.lukacko@teckon.sk<br/>0910 216 123', s_small),
        Paragraph(f'<b>{T["accepted_by"]}</b>', s_small),
    ]], colWidths=[85*mm, 87*mm])
    sig_tbl.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'TOP')]))
    story.append(sig_tbl)

    doc.build(story)
    pdf_bytes = buf.getvalue()

    response = make_response(pdf_bytes)
    response.headers['Content-Type'] = 'application/pdf'
    response.headers['Content-Disposition'] = f'attachment; filename="Preisangebot_{quote_number}.pdf"'
    return response


if __name__ == '__main__':
    app.run(host='0.0.0.0', debug=True, port=5050)
