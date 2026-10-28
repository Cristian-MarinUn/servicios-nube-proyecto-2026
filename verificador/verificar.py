#!/usr/bin/env python3
"""
Verificador automático – Entrega 1 (AWS) – Servicios en la Nube

Prueba desde internet la infraestructura que cada grupo montó para la intranet
de NexaCloud y calcula el puntaje técnico de la rúbrica. Solo usa la librería
estándar de Python 3.8+ (no hay que instalar nada).

Uso:
    python3 verificar.py                       # usa ./config.json
    python3 verificar.py --config otro.json
    python3 verificar.py --validar             # solo revisa que config.json esté completo y que las direcciones respondan
    python3 verificar.py --seccion balanceador # una sola sección
    python3 verificar.py --seccion carga       # prueba de carga: enciende el CPU del servidor (con --aws espera la alarma)
    python3 verificar.py --aws                 # autoevaluación del monitoreo y de la seguridad (necesita el CLI de AWS con sus credenciales; no suma puntos)

Notas:
- La sección "nuevo" inserta dos empleados de prueba en la base de datos.
- Las secciones "galeria" y "balanceador" intentan escribir un archivo de prueba en cada bucket sin
  credenciales: si el bucket está bien cerrado, la escritura se rechaza y no queda nada.
"""
import argparse
import concurrent.futures
import html
import ipaddress
import json
import re
import shutil
import socket
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
from datetime import datetime, timezone

SECCIONES = ["app", "empleados", "galeria", "nuevo", "balanceador", "seguridad", "monitoreo", "carga"]
# «carga» no corre por defecto: enciende el CPU del servidor durante minutos (use --seccion carga)
SECCIONES_POR_DEFECTO = [x for x in SECCIONES if x != "carga"]

# Correos de los 21 empleados de ejemplo (database/ddl-empleado.sql)
CORREOS_BASE = [
    "ana.lopez@example.com", "carlos@example.com", "sofia@example.com", "diego@example.com",
    "laura@example.com", "pedro@example.com", "isabel@example.com", "miguel@example.com",
    "carolina@example.com", "andres@example.com", "valeria@example.com", "elena@example.com",
    "roberto@example.com", "fernanda@example.com", "julio@example.com", "patricia@example.com",
    "raul@example.com", "natalia@example.com", "andrea@example.com", "hugo@example.com",
    "silvia@example.com",
]

ID_INSTANCIA = re.compile(r"\bi-[0-9a-f]{8,17}\b")

# Una imagen subida a S3 sin tipo de contenido queda como octet-stream; el navegador igual la muestra.
TIPOS_GENERICOS = ("application/octet-stream", "binary/octet-stream")
EXT_IMAGEN = (".jpg", ".jpeg", ".png", ".gif", ".webp", ".svg", ".bmp", ".avif")

# Nombres de archivo típicos de una página de error, para probar si se leen sin autorización
CLAVES_ERROR = ("index.html", "error.html", "503.html", "502.html", "500.html", "404.html", "error/index.html")

# Textos de las páginas de error por defecto (balanceador, nginx, Apache)
ERROR_POR_DEFECTO = re.compile(
    r"bad gateway|service (temporarily )?unavailable|gateway time-?out|welcome to nginx|apache2 .*default page|it works!?",
    re.I)

USE_COLOR = sys.stdout.isatty()

# Descuento sobre la nota (escala 0-5) por cada problema de seguridad: SSH, puerto del RDS y bucket abierto
DESCUENTO = 0.2
# Descuento si la prueba de carga de la app no funciona (stress no instalado, no arranca o el CPU no sube)
DESCUENTO_CARGA = 0.3
# CPU (%) que debe alcanzar el servidor durante la prueba de carga
UMBRAL_CARGA = 60


def color(texto, codigo):
    return f"\033[{codigo}m{texto}\033[0m" if USE_COLOR else texto


# ----------------------------------------------------------------------------
# Utilidades
# ----------------------------------------------------------------------------

def http(metodo, url, headers=None, cuerpo=None, timeout=15):
    """Devuelve (estado, encabezados, cuerpo_bytes). estado=None si no hubo respuesta."""
    cab = {"User-Agent": "verificador-nexacloud/1.0"}
    cab.update(headers or {})
    req = urllib.request.Request(url, data=cuerpo, method=metodo, headers=cab)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return r.status, dict(r.headers), r.read()
    except urllib.error.HTTPError as e:
        return e.code, dict(e.headers), e.read()
    except Exception as e:  # noqa: BLE001
        return None, {}, str(e).encode()


def texto(cuerpo):
    return html.unescape(cuerpo.decode("utf-8", errors="replace"))


def unir(base, ruta):
    return base.rstrip("/") + ruta


class Resultados:
    def __init__(self):
        self.filas = []  # dicts: seccion, nombre, maximo, puntos (None = no evaluado), detalle
        self.descuentos = {}  # clave -> (motivo, valor): se restan de la nota (escala 0-5), una vez por clave
        self.revisar = {}  # clave -> texto: lo que el script no puede decidir solo y debe mirar el profesor

    def por_revisar(self, clave, texto_):
        self.revisar.setdefault(clave, texto_)

    def descontar(self, clave, motivo, valor=None):
        """Descuento sobre la nota (escala 0-5). Cada clave descuenta una sola vez."""
        self.descuentos.setdefault(clave, (motivo, DESCUENTO if valor is None else valor))

    def agregar(self, seccion, nombre, maximo, fraccion, detalle="", informativo=False):
        """fraccion en [0,1] o None si no se evaluó. Las filas informativas no suman puntos."""
        if informativo:
            self.filas.append({"seccion": seccion, "nombre": nombre, "maximo": 0, "puntos": None,
                               "informativo": True, "cumple": bool(fraccion), "detalle": detalle})
            return
        puntos = None if fraccion is None else round(maximo * max(0.0, min(1.0, fraccion)), 2)
        self.filas.append({"seccion": seccion, "nombre": nombre, "maximo": maximo,
                           "puntos": puntos, "detalle": detalle})


def bucket_estado(bucket):
    """Prueba anónima de un bucket: 'privado', 'publico', 'no_existe' o 'indeterminado'."""
    estado, _, cuerpo = http("GET", f"https://{bucket}.s3.amazonaws.com/?list-type=2")
    if estado == 403:
        return "privado", "el listado anónimo está denegado (403)"
    if estado == 200:
        return "publico", "cualquiera puede listar el bucket (200)"
    if estado == 404 or b"NoSuchBucket" in cuerpo:
        return "no_existe", "el bucket no existe (revise el nombre en config.json)"
    return "indeterminado", f"respuesta inesperada ({estado})"


def bucket_sin_acceso_anonimo(bucket, region, claves=()):
    """Escritura anónima y lectura anónima de archivos conocidos. Devuelve (cerrado, detalle).

    Usa la dirección regional del bucket; si la región del config.json no es la del bucket, S3
    responde con una redirección y la prueba no concluye (se da por cerrado el bucket)."""
    base = f"https://{bucket}.s3.{region}.amazonaws.com"
    nombre = f"verificador-{uuid.uuid4().hex[:8]}.txt"
    est, _, _ = http("PUT", f"{base}/{nombre}", {"Content-Type": "text/plain"}, b"prueba del verificador")
    if est in (200, 201, 204):
        http("DELETE", f"{base}/{nombre}")
        return False, "cualquiera puede escribir en el bucket (se aceptó un PUT sin credenciales)"
    for clave in claves:
        e, _, _ = http("GET", f"{base}/{clave}")
        if e == 200:
            return False, f"el archivo «{clave}» se abre sin autorización"
    return True, ""


def error_generico(cabeceras, cuerpo):
    """Por qué la respuesta sin ID de instancia parece una página de error por defecto y no una hecha
    por el grupo. Devuelve el motivo, o '' si parece una página propia."""
    # No se usa la cabecera Server: el balanceador la pone también en las páginas propias del grupo.
    if len(cuerpo) < 50:
        return f"la respuesta está vacía o casi ({len(cuerpo)} bytes)"
    if len(cuerpo) < 2000 and ERROR_POR_DEFECTO.search(texto(cuerpo)):
        return "el texto es el de una página de error por defecto del balanceador o de un servidor"
    return ""


def pedir_balanceador(url, i):
    """(clase, motivo_generico, estado). clase: ID de instancia, 'ERROR' (sin ID) o None (sin respuesta).
    motivo_generico: por qué una respuesta de error parece por defecto ('' si parece propia)."""
    e, cab, cu = http("GET", f"{url.rstrip('/')}/?n={i}-{uuid.uuid4().hex[:6]}", timeout=10)
    if e is None:
        return None, "", None
    ids = ID_INSTANCIA.findall(texto(cu))
    if ids:
        return ids[0], "", e
    return "ERROR", error_generico(cab, cu), e


def servidores_del_balanceador(cfg, ctx, n=30):
    """IDs de instancia que entrega el balanceador (los de la sección «balanceador» si ya corrió)."""
    if "servidores" not in ctx:
        with concurrent.futures.ThreadPoolExecutor(max_workers=10) as pool:
            clases = [c for c, *_ in pool.map(lambda i: pedir_balanceador(cfg["balanceador_url"], i), range(n))]
        ctx["servidores"] = sorted({c for c in clases if c not in (None, "ERROR")})
    return ctx["servidores"]


# ----------------------------------------------------------------------------
# Secciones
# ----------------------------------------------------------------------------

def sec_app(cfg, res, ctx):
    s = "App"
    estado, _, cuerpo = http("GET", unir(cfg["app_url"], "/empresa"))
    res.agregar(s, "La app responde en /empresa", 5, 1 if estado == 200 else 0,
                f"HTTP {estado}" if estado else "no hay respuesta: " + cuerpo.decode(errors="replace")[:80])
    esta = estado == 200 and cfg["nombre_empresa"].lower() in texto(cuerpo).lower()
    res.agregar(s, "Muestra el nombre de la empresa", 5, 1 if esta else 0,
                "" if esta else f"no se encontró «{cfg['nombre_empresa']}» en la página")
    est, _, cu = http("GET", unir(cfg["app_url"], "/api/estado"))
    if est == 200:
        try:
            ctx["instancia"] = json.loads(cu).get("instancia")
        except ValueError:
            pass


def sec_empleados(cfg, res, ctx):
    s = "Empleados"
    estado, _, cuerpo = http("GET", unir(cfg["app_url"], "/empleados"))
    res.agregar(s, "La página responde", 3, 1 if estado == 200 else 0, f"HTTP {estado}")
    if estado != 200:
        res.agregar(s, "Muestra los empleados de la base de datos", 12, 0, "la página no cargó")
        return
    pagina = texto(cuerpo).lower()
    hallados = sum(1 for c in CORREOS_BASE if c in pagina)
    res.agregar(s, "Muestra los empleados de la base de datos", 12, hallados / len(CORREOS_BASE),
                f"{hallados} de {len(CORREOS_BASE)} empleados de ejemplo")


def sec_galeria(cfg, res, ctx):
    s = "Galería"
    estado, _, cuerpo = http("GET", unir(cfg["app_url"], "/galeria"))
    imgs_pagina = re.findall(r'<img[^>]+src="([^"]+)"', texto(cuerpo)) if estado == 200 else []
    res.agregar(s, "La página muestra imágenes", 3, 1 if imgs_pagina else 0,
                f"{len(imgs_pagina)} imágenes en la página" if estado == 200 else f"HTTP {estado}")

    est, _, cu = http("GET", cfg["api_imagenes_url"], {"x-api-key": cfg["api_key"]})
    urls = []
    if est == 200:
        try:
            urls = [u for u in json.loads(cu).get("images", []) if isinstance(u, str)]
        except (ValueError, AttributeError):
            urls = []
    res.agregar(s, "La API entrega {\"images\": [...]} con la API key", 3, 1 if urls else 0,
                f"HTTP {est}, {len(urls)} URLs")

    muestra = (urls or imgs_pagina)[:6]
    abren = 0
    for u in muestra:
        e, h, _ = http("GET", u)
        tipo = next((v for k, v in h.items() if k.lower() == "content-type"), "")
        sin_consulta = urllib.parse.urlparse(u).path.lower()
        if e == 200 and (tipo.startswith("image/")
                         or (tipo.split(";")[0].strip() in TIPOS_GENERICOS and sin_consulta.endswith(EXT_IMAGEN))):
            abren += 1
    res.agregar(s, "Las URLs de las imágenes abren desde el navegador", 3,
                (abren / len(muestra)) if muestra else 0, f"{abren} de {len(muestra)} abren")

    est_sin, _, _ = http("GET", cfg["api_imagenes_url"])
    res.agregar(s, "La API rechaza peticiones sin API key", 3, 1 if est_sin in (401, 403) else 0,
                f"sin llave respondió HTTP {est_sin}")

    estado_b, detalle = bucket_estado(cfg["bucket_imagenes"])
    privado = estado_b == "privado"
    abierto = estado_b == "publico"
    if privado and muestra:
        # el objeto sin firma tampoco debe abrirse
        sin_firma = muestra[0].split("?")[0]
        e, _, _ = http("GET", sin_firma)
        if e == 200:
            privado, abierto, detalle = False, True, "los objetos se abren sin URL firmada"
    if privado:
        cerrado, det_anonimo = bucket_sin_acceso_anonimo(cfg["bucket_imagenes"], cfg.get("region", "us-east-1"))
        if not cerrado:
            privado, abierto, detalle = False, True, det_anonimo
    res.agregar(s, "El bucket de imágenes no es público", 3, 1 if privado else 0, detalle)
    if abierto:
        res.descontar("bucket", f"bucket de imágenes abierto: {detalle}")


def sec_nuevo(cfg, res, ctx):
    s = "Nuevo empleado"
    marca = uuid.uuid4().hex[:8]

    def cuerpo(correo):
        return json.dumps({
            "nombre": "Verificación", "apellido": f"Automática {marca}",
            "fecha_nacimiento": "1990-01-01", "direccion": "Calle de prueba 1",
            "correo_electronico": correo, "cargo": "Prueba automática",
        }).encode()

    cab = {"Content-Type": "application/json"}
    est_sin, _, _ = http("POST", cfg["api_registro_url"], cab, cuerpo(f"sin-llave-{marca}@verificacion.test"))
    res.agregar(s, "La API rechaza peticiones sin API key", 4, 1 if est_sin in (401, 403) else 0,
                f"sin llave respondió HTTP {est_sin}")

    correo_api = f"api-{marca}@verificacion.test"
    est, _, cu = http("POST", cfg["api_registro_url"], {**cab, "x-api-key": cfg["api_key"]}, cuerpo(correo_api))
    res.agregar(s, "La API registra con la API key (2xx)", 4, 1 if est and 200 <= est < 300 else 0,
                f"HTTP {est} {cu.decode(errors='replace')[:80]}")

    correo_app = f"app-{marca}@verificacion.test"
    est_app, _, _ = http("POST", unir(cfg["app_url"], "/api/empleados"), cab, cuerpo(correo_app))
    res.agregar(s, "El formulario de la app registra (2xx)", 2, 1 if est_app and 200 <= est_app < 300 else 0,
                f"HTTP {est_app}")

    aparece = False
    for _ in range(6):
        e, _, cu2 = http("GET", unir(cfg["app_url"], "/empleados"))
        if e == 200 and correo_app in texto(cu2).lower():
            aparece = True
            break
        time.sleep(2)
    res.agregar(s, "El empleado registrado aparece en el directorio", 5, 1 if aparece else 0,
                "" if aparece else "no apareció en /empleados")


def sec_balanceador(cfg, res, ctx):
    s = "Balanceador"
    n = ctx["muestras"]
    url = cfg["balanceador_url"]

    with concurrent.futures.ThreadPoolExecutor(max_workers=10) as pool:
        respuestas = list(pool.map(lambda i: pedir_balanceador(url, i), range(n)))
    validas = [c for c, *_ in respuestas if c is not None]
    genericas = sum(1 for c, motivo, _ in respuestas if c == "ERROR" and motivo)
    propias = [e for c, motivo, e in respuestas if c == "ERROR" and not motivo]  # códigos HTTP de las páginas propias

    if len(validas) < n * 0.9:
        res.agregar(s, "El balanceador responde", 0, 1, f"solo {len(validas)} de {n} peticiones tuvieron respuesta")
        for nombre, mx in [("Dos servidores distintos (identificador visible)", 5),
                           ("Aparece la página de error", 2),
                           ("La página de error está en un bucket privado de S3", 2),
                           ("Reparto parejo entre las tres respuestas", 6),
                           ("Las respuestas se alternan al azar", 2)]:
            res.agregar(s, nombre, mx, 0, "el balanceador no respondió")
    else:
        conteo = {}
        for r in validas:
            conteo[r] = conteo.get(r, 0) + 1
        servidores = sorted(k for k in conteo if k != "ERROR")
        ctx["servidores"] = servidores
        errores = conteo.get("ERROR", 0)
        propia = errores > 0 and (errores - genericas) > genericas

        res.agregar(s, "Dos servidores distintos (identificador visible)", 5,
                    1 if len(servidores) == 2 else 0,
                    f"identificadores vistos: {', '.join(servidores) or 'ninguno'}")
        # una página de error debe responder con un código de error (4xx o 5xx), no con 200
        con_codigo = sum(1 for e in propias if e is not None and e >= 400)
        codigo_ok = propia and con_codigo > len(propias) / 2
        detalle_error = f"{errores} de {len(validas)} respuestas sin identificador de servidor"
        if errores and not propia:
            motivos = [m for c, m, _ in respuestas if c == "ERROR" and m]
            comun = max(set(motivos), key=motivos.count) if motivos else ""
            detalle_error += f"; {genericas} parecen una página de error por defecto ({comun}), no una página propia"
        elif propia and not codigo_ok:
            codigos = sorted({e for e in propias if e is not None})
            detalle_error += (f"; tiene página propia, pero responde HTTP {', '.join(map(str, codigos))}: "
                              "una página de error debe responder un código 4xx o 5xx (por ejemplo 503), así que no cuenta")
        res.agregar(s, "Aparece la página de error", 2, 1 if codigo_ok else 0, detalle_error)

        estado_b, detalle = bucket_estado(cfg["bucket_error"])
        privado = estado_b == "privado"
        abierto = estado_b == "publico"
        if privado:
            cerrado, det_anonimo = bucket_sin_acceso_anonimo(cfg["bucket_error"], cfg.get("region", "us-east-1"),
                                                             CLAVES_ERROR)
            if not cerrado:
                privado, abierto, detalle = False, True, det_anonimo
        if privado and not propia:
            detalle = "el bucket es privado, pero la página de error que se ve no es una página propia"
        res.agregar(s, "La página de error está en un bucket privado de S3", 2,
                    1 if privado and propia else 0, detalle)
        if abierto:
            res.descontar("bucket", f"bucket de la página de error abierto: {detalle}")

        clases = (servidores + ["ERROR"]) if len(servidores) == 2 else []
        if clases:
            partes, ok = [], 0
            for c in clases:
                p = conteo.get(c, 0) / len(validas)
                dentro = 0.22 <= p <= 0.45
                ok += dentro
                partes.append(f"{'error' if c == 'ERROR' else c[-6:]}: {p:.0%}")
            res.agregar(s, "Reparto parejo entre las tres respuestas", 6, ok / 3,
                        "; ".join(partes) + "  (se espera 22 % – 45 % cada una)")
        else:
            res.agregar(s, "Reparto parejo entre las tres respuestas", 6, 0,
                        "se necesitan exactamente dos servidores y la página de error")

        cambios = sum(1 for a, b in zip(validas, validas[1:]) if a != b)
        ratio = cambios / max(1, len(validas) - 1)
        res.agregar(s, "Las respuestas se alternan al azar", 2, 1 if ratio >= 0.5 else 0,
                    f"cambia de respuesta en {ratio:.0%} de las peticiones")

    # La sección «Balanceador de carga» de la app debe estar enlazada con LOAD_BALANCER_URL
    # y debe apuntar al mismo balanceador: los servidores que muestra deben ser los que entrega balanceador_url
    conocidos = set(servidores_del_balanceador(cfg, ctx))
    visto, ajenos = False, set()
    for i in range(30):
        e, _, cu = http("GET", unir(cfg["app_url"], f"/proxy?n={i}-{uuid.uuid4().hex[:6]}"))
        ids = set(ID_INSTANCIA.findall(texto(cu))) if e is not None else set()
        if ids & conocidos:
            visto = True
            break
        ajenos |= ids
    if visto:
        detalle = ""
    elif ajenos:
        detalle = f"/proxy muestra {', '.join(sorted(ajenos))}, que el balanceador no entregó (¿LOAD_BALANCER_URL apunta a otro lado?)"
    else:
        detalle = "/proxy de la app no devolvió la página de un servidor del balanceador"
    res.agregar(s, "La app consulta el balanceador (LOAD_BALANCER_URL)", 3, 1 if visto else 0, detalle)


MUNDO = ("0.0.0.0/0", "::/0")
PUERTO_RDS = 9876
# Puertos que pueden estar abiertos a todo internet en cada componente
ABIERTOS_APP = {80, 443, 3000}
ABIERTOS_BALANCEADOR = {80, 443}


def sondear(host, puerto, timeout=5):
    """('abierto', banner) | ('cerrado', '') | ('sin_respuesta', '') desde este computador."""
    try:
        with socket.create_connection((host, puerto), timeout=timeout) as c:
            c.settimeout(3)
            try:
                banner = c.recv(64).decode("ascii", errors="replace").strip()
            except OSError:
                banner = ""
            return "abierto", banner
    except ConnectionRefusedError:
        return "cerrado", ""
    except OSError:
        return "sin_respuesta", ""


def reglas_abiertas(sg):
    """Reglas de entrada de un security group abiertas a todo internet: [(protocolo, desde, hasta)]."""
    salida = []
    for r in sg.get("IpPermissions", []):
        origenes = [x.get("CidrIp") for x in r.get("IpRanges", [])] + [x.get("CidrIpv6") for x in r.get("Ipv6Ranges", [])]
        if any(o in MUNDO for o in origenes):
            proto = r.get("IpProtocol")
            todo = proto == "-1"
            salida.append((proto, 0 if todo else r.get("FromPort", 0), 65535 if todo else r.get("ToPort", 65535)))
    return salida


def origenes_regla(permiso):
    """Orígenes de una regla de entrada: bloques CIDR y security groups."""
    return ([x.get("CidrIp") for x in permiso.get("IpRanges", [])]
            + [x.get("CidrIpv6") for x in permiso.get("Ipv6Ranges", [])]
            + [f"grupo {x.get('GroupId')}" for x in permiso.get("UserIdGroupPairs", [])])


def cubre(regla, puerto):
    proto, desde, hasta = regla
    return proto in ("-1", "tcp") and desde <= puerto <= hasta


def regla_txt(regla):
    proto, desde, hasta = regla
    if proto == "-1":
        return "todo el tráfico"
    return f"{proto} {desde}" if desde == hasta else f"{proto} {desde}-{hasta}"


def instancia_de_la_app(cfg, ctx):
    if not ctx.get("instancia"):
        est, _, cu = http("GET", unir(cfg["app_url"], "/api/estado"))
        if est == 200:
            try:
                ctx["instancia"] = json.loads(cu).get("instancia")
            except ValueError:
                pass
    return ctx.get("instancia") or ""


def recolectar_aws(cfg, ctx, region, rds_endpoint):
    """Security groups por componente y datos del RDS, con el CLI de AWS."""
    def de_instancias(ids):
        if not ids:
            return set()
        r = aws(["ec2", "describe-instances", "--instance-ids", *ids], region)
        return {g["GroupId"] for rv in r.get("Reservations", []) for i in rv.get("Instances", [])
                for g in i.get("SecurityGroups", [])}

    grupos = {"app": de_instancias([instancia_de_la_app(cfg, ctx)] if instancia_de_la_app(cfg, ctx) else []),
              "servidores": de_instancias(servidores_del_balanceador(cfg, ctx))}

    dbs = aws(["rds", "describe-db-instances"], region).get("DBInstances", [])
    if rds_endpoint:
        elegidas = [d for d in dbs if d.get("Endpoint", {}).get("Address", "").lower() == rds_endpoint.lower()]
    else:
        elegidas = [d for d in dbs if "postgres" in d.get("Engine", "")]
    rds = elegidas[0] if len(elegidas) == 1 else None
    grupos["rds"] = {v["VpcSecurityGroupId"] for v in rds.get("VpcSecurityGroups", [])} if rds else set()

    host_lb = (urllib.parse.urlparse(cfg["balanceador_url"]).hostname or "").lower()
    lbs = aws(["elbv2", "describe-load-balancers"], region).get("LoadBalancers", [])
    lb = next((x for x in lbs if x.get("DNSName", "").lower() == host_lb), None)
    grupos["balanceador"] = set(lb.get("SecurityGroups", [])) if lb else set()

    todos = sorted(set().union(*grupos.values()))
    por_id = {}
    if todos:
        por_id = {g["GroupId"]: g for g in aws(["ec2", "describe-security-groups", "--group-ids", *todos],
                                               region).get("SecurityGroups", [])}
    return {rol: [por_id[i] for i in ids if i in por_id] for rol, ids in grupos.items()}, rds


def sec_seguridad(cfg, res, ctx):
    """Autoevaluación de RDS, security groups y SSH. No suma puntos."""
    s = "Seguridad (autoevaluación, no suma puntos)"
    region = cfg.get("region", "us-east-1")
    host_app = urllib.parse.urlparse(cfg["app_url"]).hostname
    rds_endpoint = str(cfg.get("rds_endpoint", "")).strip()
    try:
        ssh = int(cfg["ssh_puerto"]) if str(cfg.get("ssh_puerto", "")).strip() else None
    except ValueError:
        ssh = None
        res.agregar(s, "ssh_puerto del config.json", 0, 0, "debe ser un número, por ejemplo 2222", informativo=True)

    grupos, rds = {}, None
    if ctx["usar_aws"]:
        if shutil.which("aws") is None:
            res.agregar(s, "CLI de AWS disponible", 0, 0, "no se encontró el comando aws", informativo=True)
        else:
            try:
                grupos, rds = recolectar_aws(cfg, ctx, region, rds_endpoint)
            except Exception as e:  # noqa: BLE001
                res.agregar(s, "Consulta a AWS", 0, 0, f"no se pudo consultar: {e}", informativo=True)
    else:
        print(color("  (security groups y puerto del RDS omitidos: use --aws)", "90"))
    if not rds_endpoint and rds:
        rds_endpoint = rds.get("Endpoint", {}).get("Address", "")

    # --- Base de datos ---
    if rds_endpoint:
        try:
            ip = socket.gethostbyname(rds_endpoint)
            privada = ipaddress.ip_address(ip).is_private
        except (OSError, ValueError):
            ip, privada = "", False
        estado_p, _ = sondear(rds_endpoint, PUERTO_RDS)
        cerrado = estado_p != "abierto"
        res.agregar(s, f"El RDS no es accesible desde internet (puerto {PUERTO_RDS})", 0, cerrado,
                    (f"resuelve a {ip} " + ("(IP privada)" if privada else "(IP pública)") + "; " if ip else "")
                    + ("el puerto no responde desde fuera" if cerrado else "el puerto responde desde internet"),
                    informativo=True)
    else:
        print(color("  (RDS omitido: falta rds_endpoint en el config.json, o use --aws)", "90"))
    if rds:
        puerto = rds.get("Endpoint", {}).get("Port")
        res.agregar(s, f"El RDS escucha en el puerto {PUERTO_RDS}", 0, puerto == PUERTO_RDS,
                    f"puerto configurado: {puerto}", informativo=True)
        if puerto != PUERTO_RDS:
            res.descontar("rds", f"el RDS escucha en el puerto {puerto}, no en el {PUERTO_RDS}")
        res.agregar(s, "El RDS no tiene acceso público (PubliclyAccessible = false)", 0,
                    not rds.get("PubliclyAccessible", True), f"PubliclyAccessible = {rds.get('PubliclyAccessible')}",
                    informativo=True)
    elif ctx["usar_aws"] and grupos:
        print(color("  (RDS no encontrado: indique rds_endpoint en el config.json)", "90"))

    # --- SSH ---
    est22, banner22 = sondear(host_app, 22)
    res.agregar(s, "El puerto 22 de la app no responde desde este computador", 0, est22 != "abierto",
                f"puerto 22: {est22.replace('_', ' ')}" + (f" ({banner22})" if banner22 else ""), informativo=True)
    if ssh is None:
        print(color("  (SSH en otro puerto omitido: falta ssh_puerto en el config.json)", "90"))
    elif ssh == 22:
        print(color("  (ssh_puerto es 22: lo que importa es a quién se lo abre el security group; use --aws para verlo)", "90"))
    else:
        est, banner = sondear(host_app, ssh)
        if est == "abierto" and banner.startswith("SSH-"):
            res.agregar(s, f"SSH atiende en el puerto {ssh} (distinto al 22)", 0, 1, banner, informativo=True)
        else:
            # sin respuesta desde aquí: ¿hay al menos una regla de entrada para ese puerto en la app?
            reglas = [p for sg in grupos.get("app", []) for p in sg.get("IpPermissions", [])
                      if cubre((p.get("IpProtocol"), p.get("FromPort", 0), p.get("ToPort", 65535)), ssh)]
            if reglas:
                res.agregar(s, f"SSH atiende en el puerto {ssh} (distinto al 22)", 0, 1,
                            "hay una regla para ese puerto, pero no responde desde aquí (¿acceso restringido a una IP?)",
                            informativo=True)
            elif grupos:
                res.agregar(s, f"SSH atiende en el puerto {ssh} (distinto al 22)", 0, 0,
                            "no responde y el security group de la app no tiene una regla para ese puerto", informativo=True)
            else:
                print(color(f"  (el puerto {ssh} no responde desde aquí, quizá por estar restringido a una IP; use --aws para revisar el security group)", "90"))

    # --- Security groups (necesitan --aws) ---
    if not grupos:
        if est22 == "abierto":
            res.por_revisar("ssh22", "El puerto 22 responde desde este computador: puede estar abierto a todo internet "
                            "o restringido a un origen que incluye esta red. Pida la captura del security group "
                            "(regla de entrada del puerto 22) o ejecute con --aws con las credenciales del grupo")
        return

    def revisar(rol, etiqueta, permitidos):
        sgs = grupos.get(rol, [])
        if not sgs:
            print(color(f"  ({etiqueta}: no se encontró)", "90"))
            return
        malas = [f"{sg['GroupName']}: {regla_txt(r)}" for sg in sgs for r in reglas_abiertas(sg)
                 if not (r[0] == "tcp" and r[1] == r[2] and r[1] in permitidos)]
        res.agregar(s, f"{etiqueta}: solo abre a internet lo necesario", 0, not malas,
                    "; ".join(malas) or "ninguna regla abierta de más", informativo=True)

    extra = {ssh} if ssh and ssh != 22 else set()
    revisar("app", "Security group de la app", ABIERTOS_APP | extra)
    revisar("balanceador", "Security group del balanceador", ABIERTOS_BALANCEADOR)
    revisar("servidores", "Security group de los servidores web (el tráfico debe entrar por el balanceador)", extra)
    revisar("rds", "Security group del RDS", set())
    fuera = [f"{sg['GroupName']}: {p.get('IpProtocol')} {p.get('FromPort')}-{p.get('ToPort')}"
             for sg in grupos.get("rds", []) for p in sg.get("IpPermissions", [])
             if not (p.get("IpProtocol") == "tcp" and p.get("FromPort") == p.get("ToPort") == PUERTO_RDS)]
    if grupos.get("rds"):
        res.agregar(s, f"El security group del RDS solo admite el puerto {PUERTO_RDS}", 0, not fuera,
                    "; ".join(fuera) or "", informativo=True)
    en_22 = [f"{sg['GroupName']}: {regla_txt(r)}" for rol in ("app", "servidores") for sg in grupos.get(rol, [])
             for r in reglas_abiertas(sg) if cubre(r, 22)]
    restringidos = sorted({o for rol in ("app", "servidores") for sg in grupos.get(rol, [])
                           for p in sg.get("IpPermissions", [])
                           if cubre((p.get("IpProtocol"), p.get("FromPort", 0), p.get("ToPort", 65535)), 22)
                           and not any(o in MUNDO for o in origenes_regla(p))
                           for o in origenes_regla(p)})
    if en_22:
        detalle_22 = "; ".join(sorted(set(en_22)))
    elif restringidos:
        detalle_22 = "puerto 22 restringido a su origen: " + ", ".join(restringidos)
    else:
        detalle_22 = "no hay regla de entrada para el puerto 22"
    res.agregar(s, "Ningún security group deja el puerto 22 abierto a todo internet", 0, not en_22,
                detalle_22, informativo=True)
    if en_22:
        res.descontar("ssh", "un security group deja el puerto 22 abierto a todo internet")


def sec_carga(cfg, res, ctx):
    """Dispara la prueba de carga de la app (POST /api/carga) y comprueba que el CPU sube.
    Con --aws espera además a que la alarma de CPU del servidor pase a ALARM."""
    s = "Prueba de carga"
    segundos = ctx["carga_segundos"]
    app = cfg["app_url"]

    def estado():
        e, _, cu = http("GET", unir(app, "/api/estado"))
        if e != 200:
            return None
        try:
            return json.loads(cu)
        except ValueError:
            return None

    antes = estado()
    if antes is None:
        res.agregar(s, "La app responde en /api/estado", 0, 0, "no se pudo probar la carga", informativo=True)
        res.por_revisar("carga", "No se pudo probar la prueba de carga: la app no respondió en /api/estado")
        return
    cpu_antes = antes.get("cpuPorcentaje", 0)
    instancia = antes.get("instancia") or ""
    ctx["instancia"] = instancia

    inicio = datetime.now(timezone.utc)
    est, _, cu = http("POST", unir(app, f"/api/carga?segundos={segundos}"), {}, b"", timeout=30)
    try:
        cuerpo = json.loads(cu)
    except ValueError:
        cuerpo = {}
    if est == 500 and cuerpo.get("code") == "STRESS_NO_INSTALADO":
        res.agregar(s, "El comando stress está instalado", 0, 0, str(cuerpo.get("message", ""))[:120], informativo=True)
        res.descontar("carga", "el comando stress no está instalado en el servidor", DESCUENTO_CARGA)
        return
    if est not in (202, 409):  # 409: ya había una prueba en curso
        res.agregar(s, "La prueba de carga arranca", 0, 0, f"HTTP {est}", informativo=True)
        res.descontar("carga", f"la prueba de carga no arrancó (HTTP {est})", DESCUENTO_CARGA)
        return
    res.agregar(s, "La prueba de carga arranca", 0, 1, f"instancia {instancia}, {segundos} s", informativo=True)

    pico = cpu_antes
    for _ in range(max(1, min(segundos, 90) // 3)):
        time.sleep(3)
        e = estado()
        if e:
            pico = max(pico, e.get("cpuPorcentaje", 0))
        if pico >= UMBRAL_CARGA:
            break
    sube = pico >= UMBRAL_CARGA and pico > cpu_antes
    res.agregar(s, f"El CPU del servidor sube durante la prueba (al menos {UMBRAL_CARGA} %)", 0, sube,
                f"antes {cpu_antes} %, pico {pico} %", informativo=True)
    if not sube:
        res.descontar("carga", f"el CPU no subió durante la prueba (pico {pico} %)", DESCUENTO_CARGA)

    if not ctx["usar_aws"]:
        return
    if shutil.which("aws") is None:
        res.agregar(s, "CLI de AWS disponible", 0, 0, "no se encontró el comando aws", informativo=True)
        return
    region = cfg.get("region", "us-east-1")
    print(color("  … esperando la alarma de CPU (puede tardar varios minutos)", "90"), flush=True)
    detalle, disparada, hay_alarma = "", False, True
    for _ in range(max(1, (segundos + 360) // 20)):
        try:
            alarmas = aws(["cloudwatch", "describe-alarms", "--alarm-types", "MetricAlarm"], region).get("MetricAlarms", [])
        except Exception as e:  # noqa: BLE001
            res.agregar(s, "Consulta a CloudWatch", 0, 0, f"no se pudo consultar: {e}", informativo=True)
            return
        cpu = [a for a in alarmas if a.get("MetricName") == "CPUUtilization"
               and any(d.get("Name") == "InstanceId" and d.get("Value") == instancia for d in a.get("Dimensions", []))]
        if not cpu:
            hay_alarma = False
            break
        for a in cpu:
            if a.get("StateValue") != "ALARM":
                continue
            try:
                desde = datetime.fromisoformat(str(a.get("StateUpdatedTimestamp")).replace("Z", "+00:00"))
                reciente = desde >= inicio
            except ValueError:
                reciente = True
            if reciente:
                disparada, detalle = True, f"{a.get('AlarmName')} pasó a ALARM"
            else:
                detalle = f"{a.get('AlarmName')} ya estaba en ALARM antes de la prueba"
        if disparada:
            break
        time.sleep(20)
    if not hay_alarma:
        res.agregar(s, "La alarma de CPU se dispara con la prueba de carga", 0, 0,
                    f"no hay alarma de CPU sobre la instancia {instancia or 'desconocida'}", informativo=True)
    else:
        res.agregar(s, "La alarma de CPU se dispara con la prueba de carga", 0, disparada,
                    detalle or f"no pasó a ALARM con {segundos} s de carga; con un periodo largo pruebe --carga-segundos 600",
                    informativo=True)


def validar(cfg):
    """Revisa que cada dirección del config.json responda. No califica nada."""
    pruebas = [
        ("app_url", lambda: http("GET", unir(cfg["app_url"], "/empresa"))[0], lambda e: e == 200),
        ("balanceador_url", lambda: http("GET", cfg["balanceador_url"])[0], lambda e: e is not None),
        ("api_imagenes_url", lambda: http("GET", cfg["api_imagenes_url"], {"x-api-key": cfg["api_key"]})[0], lambda e: e == 200),
        ("api_registro_url", lambda: http("GET", cfg["api_registro_url"])[0], lambda e: e is not None),
        ("bucket_imagenes", lambda: bucket_estado(cfg["bucket_imagenes"])[0], lambda e: e != "no_existe"),
        ("bucket_error", lambda: bucket_estado(cfg["bucket_error"])[0], lambda e: e != "no_existe"),
    ]
    todo_bien = True
    for campo, accion, bien in pruebas:
        r = accion()
        ok = bien(r)
        todo_bien &= ok
        print(f"  {color('✔', '32') if ok else color('✘', '31')} {campo}: {r if r is not None else 'sin respuesta'}")
    print("\nLa configuración parece correcta." if todo_bien else "\nRevise las direcciones marcadas con ✘ en config.json.")
    return todo_bien


def aws(args, region):
    r = subprocess.run(["aws", *args, "--region", region, "--output", "json"],
                       capture_output=True, text=True, timeout=60)
    if r.returncode != 0:
        raise RuntimeError(r.stderr.strip()[:200])
    return json.loads(r.stdout or "{}")


def sec_monitoreo(cfg, res, ctx):
    """Autoevaluación del monitoreo. No suma puntos: el profesor lo califica con el correo de alerta."""
    s = "Monitoreo (autoevaluación, no suma puntos)"
    if not ctx["usar_aws"]:
        print(color("  (monitoreo omitido: use --aws para revisar su alarma y su suscripción)", "90"))
        return
    if shutil.which("aws") is None:
        res.agregar(s, "CLI de AWS disponible", 0, 0, "no se encontró el comando aws", informativo=True)
        return

    region = cfg.get("region", "us-east-1")
    instancia = ctx.get("instancia") or ""
    try:
        alarmas = aws(["cloudwatch", "describe-alarms", "--alarm-types", "MetricAlarm"], region).get("MetricAlarms", [])
    except Exception as e:  # noqa: BLE001
        res.agregar(s, "Consulta a CloudWatch", 0, 0, f"no se pudo consultar: {e}", informativo=True)
        return

    cpu = [a for a in alarmas if a.get("MetricName") == "CPUUtilization"
           and any(d.get("Name") == "InstanceId" and d.get("Value") == instancia for d in a.get("Dimensions", []))]
    res.agregar(s, "Existe una alarma de CPU sobre el servidor de la app", 0, bool(cpu),
                f"instancia de la app: {instancia or 'desconocida'}; alarmas de CPU encontradas: {len(cpu)}",
                informativo=True)

    temas = sorted({t for a in cpu for t in a.get("AlarmActions", []) if ":sns:" in t})
    res.agregar(s, "La alarma notifica a un tema de SNS", 0, bool(temas),
                ", ".join(temas) or "la alarma no tiene acción de SNS", informativo=True)

    confirmada = False
    for t in temas:
        try:
            subs = aws(["sns", "list-subscriptions-by-topic", "--topic-arn", t], region).get("Subscriptions", [])
        except Exception:  # noqa: BLE001
            continue
        if any(x.get("Protocol") == "email" and x.get("SubscriptionArn", "").startswith("arn:") for x in subs):
            confirmada = True
    res.agregar(s, "El tema tiene una suscripción de correo confirmada", 0, confirmada,
                "" if confirmada else "no hay suscripción de correo confirmada", informativo=True)


FUNCIONES = {"app": sec_app, "empleados": sec_empleados, "galeria": sec_galeria,
             "nuevo": sec_nuevo, "balanceador": sec_balanceador, "seguridad": sec_seguridad,
             "monitoreo": sec_monitoreo, "carga": sec_carga}

# ----------------------------------------------------------------------------
# Programa principal
# ----------------------------------------------------------------------------

REQUERIDOS = ["nombre_empresa", "app_url", "balanceador_url", "api_imagenes_url",
              "api_registro_url", "api_key", "bucket_imagenes", "bucket_error"]


def main():
    ap = argparse.ArgumentParser(description="Verificador de la Entrega 1 (AWS)")
    ap.add_argument("--config", default="config.json")
    ap.add_argument("--seccion", action="append", choices=SECCIONES,
                    help="ejecutar solo estas secciones (se puede repetir)")
    ap.add_argument("--validar", action="store_true", help="solo revisar config.json y las direcciones")
    ap.add_argument("--aws", action="store_true", help="autoevaluar el monitoreo y la seguridad (security groups, RDS) con el CLI de AWS (no suma puntos)")
    ap.add_argument("--carga-segundos", type=int, default=150, dest="carga_segundos",
                    help="duración de la prueba de carga de la sección «carga» (1 a 600, por defecto 150)")
    ap.add_argument("--muestras", type=int, default=200, help="peticiones al balanceador (por defecto 200)")
    ap.add_argument("--salida", default="resultado.json")
    args = ap.parse_args()

    try:
        with open(args.config, encoding="utf-8") as f:
            cfg = json.load(f)
    except (OSError, ValueError) as e:
        sys.exit(f"No se pudo leer {args.config}: {e}")
    faltan = [k for k in REQUERIDOS if not str(cfg.get(k, "")).strip()]
    if faltan:
        sys.exit("Faltan campos en el archivo de configuración: " + ", ".join(faltan))

    if args.validar:
        sys.exit(0 if validar(cfg) else 1)

    ctx = {"muestras": args.muestras, "usar_aws": args.aws,
           "carga_segundos": max(1, min(600, args.carga_segundos))}
    res = Resultados()
    for nombre in (args.seccion or SECCIONES_POR_DEFECTO):
        print(color(f"… {nombre}", "90"), flush=True)
        try:
            FUNCIONES[nombre](cfg, res, ctx)
        except Exception as e:  # noqa: BLE001
            res.agregar(nombre, "Error inesperado en la verificación", 0, 0, repr(e))

    # --- informe ---
    print()
    actual = None
    for f in res.filas:
        if f["seccion"] != actual:
            actual = f["seccion"]
            print(color(actual, "1"))
        if f.get("informativo"):
            marca, txt = (color("✔", "32") if f["cumple"] else color("✘", "31")), "auto"
        elif f["puntos"] is None:
            marca, txt = color("–", "33"), "n/e"
        elif f["maximo"] and f["puntos"] >= f["maximo"]:
            marca, txt = color("✔", "32"), f"{f['puntos']:g}/{f['maximo']}"
        elif f["puntos"] > 0:
            marca, txt = color("~", "33"), f"{f['puntos']:g}/{f['maximo']}"
        else:
            marca, txt = color("✘", "31"), f"0/{f['maximo']}"
        det = f"  {color(f['detalle'], '90')}" if f["detalle"] else ""
        print(f"  {marca} {txt:>7}  {f['nombre']}{det}")

    evaluado = [f for f in res.filas if f["puntos"] is not None]
    total = sum(f["puntos"] for f in evaluado)
    maximo_eval = sum(f["maximo"] for f in evaluado)
    maximo_total = sum(f["maximo"] for f in res.filas)
    print()
    print(color(f"Puntaje automático: {total:g} / {maximo_eval:g}", "1"))
    if maximo_eval != maximo_total:
        print(f"({maximo_total - maximo_eval:g} puntos no evaluados en esta corrida; máximo posible {maximo_total:g})")
    if res.descuentos:
        print()
        print(color(f"Descuentos de seguridad sobre la nota (escala 0-5): -{sum(v for _, v in res.descuentos.values()):g}", "1"))
        for motivo, valor in res.descuentos.values():
            print(f"  {color('✘', '31')} -{valor:g}  {motivo}")
    if res.revisar:
        print()
        print(color("Para revisar a mano (el script no puede decidirlo solo):", "1"))
        for texto_ in res.revisar.values():
            print(f"  {color('?', '33')} {texto_}")
    print("El monitoreo (10 puntos) lo califica el profesor con el correo de alerta que usted le reenvía.")
    print("El informe de arquitectura y la estimación de costos (15 puntos) también los califica el profesor.")

    seguro = {k: v for k, v in cfg.items() if k != "api_key"}
    with open(args.salida, "w", encoding="utf-8") as f:
        json.dump({"fecha": datetime.now().isoformat(timespec="seconds"), "config": seguro,
                   "puntaje": total, "maximo_evaluado": maximo_eval, "maximo_total": maximo_total,
                   "descuentos": [{"motivo": m, "valor": v} for m, v in res.descuentos.values()],
                   "descuento_total": round(sum(v for _, v in res.descuentos.values()), 2),
                   "revisar_a_mano": list(res.revisar.values()),
                   "verificaciones": res.filas}, f, ensure_ascii=False, indent=2)
    print(f"Detalle guardado en {args.salida}")


if __name__ == "__main__":
    main()
