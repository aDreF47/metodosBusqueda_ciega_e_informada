"""
PROYECTO: Búsqueda Informada - Algoritmo Hill Climbing con Interfaz Gráfica
Autor: Fernando Celadita
Descripción: Implementación de búsqueda informada Hill Climbing con GUI interactiva
para encontrar el camino de menor distancia en grafos direccionados.
NOTA: Hill Climbing es una búsqueda informada que utiliza heurísticas para optimización.
"""

import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext, filedialog
import time
import threading
from collections import defaultdict
import math
import json
import heapq

class Grafo:
    """
    Clase que representa un grafo direccionado con pesos en las aristas.
    Para búsqueda informada, los pesos SÍ se consideran para encontrar caminos óptimos.
    """
    
    def __init__(self):
        self.adyacencias = defaultdict(list)  # Lista de adyacencia
        self.aristas = []  # Lista de todas las aristas (origen, destino, peso)
        self.nodos = set()  # Conjunto de todos los nodos
        self.posiciones_nodos = {}  # Para calcular heurísticas de distancia euclidiana
    
    def agregar_arista(self, origen, destino, peso):
        """Agrega una arista al grafo."""
        try:
            peso = float(peso)
            self.adyacencias[origen].append((destino, peso))
            self.aristas.append((origen, destino, peso))
            self.nodos.add(origen)
            self.nodos.add(destino)
            return True
        except ValueError:
            return False
    
    def obtener_vecinos_con_peso(self, nodo):
        """
        Retorna los nodos vecinos de un nodo dado CON sus pesos.
        Para búsqueda informada, SÍ necesitamos los pesos.
        """
        return self.adyacencias[nodo]
    
    def obtener_peso(self, origen, destino):
        """
        Obtiene el peso de la arista entre dos nodos.
        Esencial para búsqueda informada.
        """
        for dest, peso in self.adyacencias[origen]:
            if dest == destino:
                return peso
        return None
    
    def calcular_heuristica_euclidiana(self, nodo, objetivo, posiciones):
        """
        Calcula la heurística de distancia euclidiana entre dos nodos.
        Útil cuando se tienen coordenadas de los nodos.
        """
        if nodo not in posiciones or objetivo not in posiciones:
            return 0  # Si no hay posiciones, usar heurística 0
        
        x1, y1 = posiciones[nodo]
        x2, y2 = posiciones[objetivo]
        return math.sqrt((x2 - x1)**2 + (y2 - y1)**2)
    
    def cargar_desde_json(self, datos_json):
        """Carga el grafo desde datos JSON con soporte para posiciones."""
        try:
            self.limpiar()
            
            if "aristas" not in datos_json:
                raise ValueError("El archivo JSON debe contener una clave 'aristas'")
            
            aristas_cargadas = 0
            errores = []
            
            # Cargar aristas
            for i, arista in enumerate(datos_json["aristas"]):
                try:
                    origen = str(arista["origen"]).strip().upper()
                    destino = str(arista["destino"]).strip().upper()
                    peso = float(arista["peso"])
                    
                    if self.agregar_arista(origen, destino, peso):
                        aristas_cargadas += 1
                    else:
                        errores.append(f"Arista {i+1}: Error al procesar {origen} -> {destino}")
                        
                except (KeyError, ValueError, TypeError) as e:
                    errores.append(f"Arista {i+1}: Formato inválido - {str(e)}")
            
            # Cargar posiciones si están disponibles (para heurísticas)
            if "posiciones" in datos_json:
                for nodo, pos in datos_json["posiciones"].items():
                    self.posiciones_nodos[str(nodo).upper()] = (pos["x"], pos["y"])
            
            return aristas_cargadas, errores
            
        except json.JSONDecodeError as e:
            raise ValueError(f"Archivo JSON inválido: {str(e)}")
        except Exception as e:
            raise ValueError(f"Error al procesar el archivo: {str(e)}")
    
    def exportar_a_json(self):
        """Exporta el grafo actual a formato JSON."""
        datos = {
            "nodos": list(self.nodos),
            "aristas": [],
            "posiciones": self.posiciones_nodos
        }
        
        for origen, destino, peso in self.aristas:
            datos["aristas"].append({
                "origen": origen,
                "destino": destino,
                "peso": peso
            })
        
        return datos
    
    def limpiar(self):
        """Limpia todos los datos del grafo."""
        self.adyacencias.clear()
        self.aristas.clear()
        self.nodos.clear()
        self.posiciones_nodos.clear()

class AlgoritmoHillClimbing:
    """
    Implementación del algoritmo de Hill Climbing (Subiendo a la Colina).
    Búsqueda informada que utiliza heurísticas para encontrar caminos óptimos.
    """
    
    def __init__(self, grafo):
        self.grafo = grafo
        self.paso_actual = 0
        self.pasos_busqueda = []
    
    def calcular_heuristica_distancia_lineal(self, nodo, objetivo):
        """
        Heurística simplificada basada en orden alfabético de nodos.
        Para casos donde no hay coordenadas disponibles.
        """
        # Convertir a valores numéricos para comparación
        nodo_val = sum(ord(c) for c in str(nodo))
        obj_val = sum(ord(c) for c in str(objetivo))
        return abs(nodo_val - obj_val) / 100  # Normalizar
    
    def buscar_camino(self, inicio, objetivo, posiciones_canvas=None):
        """
        Ejecuta Hill Climbing para encontrar el camino de menor costo.
        Utiliza heurísticas para guiar la búsqueda hacia el objetivo.
        """
        # Reiniciar estado
        self.pasos_busqueda.clear()
        self.paso_actual = 0
        
        # Verificar que los nodos existen
        if inicio not in self.grafo.nodos or objetivo not in self.grafo.nodos:
            error_paso = {
                'paso': 0,
                'accion': 'Error: Uno o ambos nodos no existen en el grafo',
                'nodo_actual': None,
                'camino_actual': [],
                'costo_total': 0,
                'visitados': set()
            }
            return None, [error_paso]
        
        # Estado inicial
        nodo_actual = inicio
        camino = [inicio]
        costo_total = 0
        visitados = {inicio}
        
        self.pasos_busqueda.append({
            'paso': 0,
            'accion': f'Iniciar Hill Climbing desde: {inicio}',
            'nodo_actual': nodo_actual,
            'camino_actual': list(camino),
            'costo_total': costo_total,
            'visitados': set(visitados)
        })
        
        paso = 1
        max_iteraciones = len(self.grafo.nodos) * 2  # Evitar bucles infinitos
        
        # Ejecutar Hill Climbing
        while nodo_actual != objetivo and paso < max_iteraciones:
            # Obtener vecinos con sus costos
            vecinos = self.grafo.obtener_vecinos_con_peso(nodo_actual)
            
            if not vecinos:
                # No hay más movimientos posibles
                self.pasos_busqueda.append({
                    'paso': paso,
                    'accion': f'Sin vecinos desde {nodo_actual} - Búsqueda fallida',
                    'nodo_actual': nodo_actual,
                    'camino_actual': list(camino),
                    'costo_total': costo_total,
                    'visitados': set(visitados)
                })
                return None, self.pasos_busqueda
            
            # Evaluar cada vecino con función de evaluación (costo + heurística)
            mejor_vecino = None
            mejor_evaluacion = float('inf')
            evaluaciones = []
            
            for vecino, peso in vecinos:
                # Evitar ciclos (opcional en Hill Climbing, pero útil)
                if vecino in visitados:
                    continue
                
                # Calcular heurística
                if posiciones_canvas:
                    heuristica = self.grafo.calcular_heuristica_euclidiana(
                        vecino, objetivo, posiciones_canvas
                    )
                else:
                    heuristica = self.calcular_heuristica_distancia_lineal(vecino, objetivo)
                
                # Función de evaluación: f(n) = g(n) + h(n)
                # g(n) = costo del camino, h(n) = heurística
                costo_nuevo = costo_total + peso
                evaluacion = costo_nuevo + heuristica
                
                evaluaciones.append({
                    'vecino': vecino,
                    'peso': peso,
                    'heuristica': heuristica,
                    'evaluacion': evaluacion
                })
                
                # Hill Climbing: elegir el mejor vecino según evaluación
                if evaluacion < mejor_evaluacion:
                    mejor_evaluacion = evaluacion
                    mejor_vecino = vecino
                    mejor_peso = peso
            
            # Registrar evaluaciones
            info_evaluaciones = ", ".join([
                f"{ev['vecino']}(f={ev['evaluacion']:.1f})" 
                for ev in evaluaciones
            ])
            
            self.pasos_busqueda.append({
                'paso': paso,
                'accion': f'Evaluar vecinos de {nodo_actual}: {info_evaluaciones}',
                'nodo_actual': nodo_actual,
                'camino_actual': list(camino),
                'costo_total': costo_total,
                'visitados': set(visitados),
                'evaluaciones': evaluaciones
            })
            paso += 1
            
            if mejor_vecino is None:
                # Todos los vecinos ya fueron visitados
                self.pasos_busqueda.append({
                    'paso': paso,
                    'accion': f'Todos los vecinos visitados - Búsqueda fallida',
                    'nodo_actual': nodo_actual,
                    'camino_actual': list(camino),
                    'costo_total': costo_total,
                    'visitados': set(visitados)
                })
                return None, self.pasos_busqueda
            
            # Moverse al mejor vecino
            nodo_actual = mejor_vecino
            camino.append(nodo_actual)
            costo_total += mejor_peso
            visitados.add(nodo_actual)
            
            accion_desc = f'Moverse a {mejor_vecino} (mejor evaluación: {mejor_evaluacion:.1f})'
            if nodo_actual == objetivo:
                accion_desc += ' - ¡OBJETIVO ALCANZADO!'
            
            self.pasos_busqueda.append({
                'paso': paso,
                'accion': accion_desc,
                'nodo_actual': nodo_actual,
                'camino_actual': list(camino),
                'costo_total': costo_total,
                'visitados': set(visitados),
                'camino_final': list(camino) if nodo_actual == objetivo else None
            })
            paso += 1
        
        if nodo_actual == objetivo:
            return camino, self.pasos_busqueda
        else:
            # Máximo de iteraciones alcanzado
            self.pasos_busqueda.append({
                'paso': paso,
                'accion': 'Máximo de iteraciones alcanzado - Búsqueda fallida',
                'nodo_actual': nodo_actual,
                'camino_actual': list(camino),
                'costo_total': costo_total,
                'visitados': set(visitados)
            })
            return None, self.pasos_busqueda

class InterfazGrafica:
    """
    Interfaz gráfica para búsqueda informada Hill Climbing.
    Muestra el proceso de búsqueda CON optimización por distancia/costo.
    """
    
    def __init__(self):
        self.ventana = tk.Tk()
        self.ventana.title("Búsqueda Informada - Hill Climbing (Subiendo a la Colina)")
        self.ventana.geometry("1200x800")
        self.ventana.configure(bg='#f0f0f0')
        
        # Datos del programa
        self.grafo = Grafo()
        self.algoritmo_hill = AlgoritmoHillClimbing(self.grafo)
        self.animacion_activa = False
        self.pasos_busqueda = []
        self.paso_actual_animacion = 0
        
        # Crear interfaz
        self._crear_interfaz()
        self._configurar_canvas()
    
    def _crear_interfaz(self):
        """Crea todos los elementos de la interfaz gráfica."""
        
        # Frame principal dividido en paneles
        frame_principal = ttk.Frame(self.ventana)
        frame_principal.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Panel izquierdo - Controles
        frame_izquierdo = ttk.Frame(frame_principal)
        frame_izquierdo.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 10))
        
        # Panel derecho - Visualización
        frame_derecho = ttk.Frame(frame_principal)
        frame_derecho.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)
        
        # === SECCIÓN: CARGA DE ARCHIVO JSON ===
        grupo_json = ttk.LabelFrame(frame_izquierdo, text="📁 Carga de Archivo JSON", padding=10)
        grupo_json.pack(fill=tk.X, pady=(0, 10))
        
        ttk.Button(grupo_json, text="📂 Cargar Grafo desde JSON", command=self._cargar_json).pack(fill=tk.X, pady=2)
        ttk.Button(grupo_json, text="💾 Exportar Grafo a JSON", command=self._exportar_json).pack(fill=tk.X, pady=2)
        
        # Información del formato JSON
        info_frame = ttk.Frame(grupo_json)
        info_frame.pack(fill=tk.X, pady=(5, 0))
        
        ttk.Button(info_frame, text="ℹ️ Ver Formato JSON", command=self._mostrar_formato_json).pack(fill=tk.X)
        
        # === SECCIÓN: ENTRADA DE DATOS MANUAL ===
        grupo_datos = ttk.LabelFrame(frame_izquierdo, text="📊 Entrada Manual de Datos", padding=10)
        grupo_datos.pack(fill=tk.X, pady=(0, 10))
        
        # Campos de entrada
        ttk.Label(grupo_datos, text="Nodo Salida:").grid(row=0, column=0, sticky=tk.W, pady=2)
        self.entry_origen = ttk.Entry(grupo_datos, width=10)
        self.entry_origen.grid(row=0, column=1, padx=5, pady=2)
        
        ttk.Label(grupo_datos, text="Nodo Entrada:").grid(row=1, column=0, sticky=tk.W, pady=2)
        self.entry_destino = ttk.Entry(grupo_datos, width=10)
        self.entry_destino.grid(row=1, column=1, padx=5, pady=2)
        
        ttk.Label(grupo_datos, text="Distancia:").grid(row=2, column=0, sticky=tk.W, pady=2)
        self.entry_peso = ttk.Entry(grupo_datos, width=10)
        self.entry_peso.grid(row=2, column=1, padx=5, pady=2)
        
        # Nota sobre búsqueda informada
        nota_label = ttk.Label(grupo_datos, text="✅ Hill Climbing OPTIMIZA por distancia\n(Búsqueda informada con heurísticas)", 
                              font=("Arial", 8), foreground="green")
        nota_label.grid(row=3, column=0, columnspan=2, pady=5)
        
        # Botones de control de datos
        ttk.Button(grupo_datos, text="Agregar Arista", command=self._agregar_arista).grid(row=4, column=0, columnspan=2, pady=5)
        ttk.Button(grupo_datos, text="Finalizar Ingreso", command=self._finalizar_ingreso).grid(row=5, column=0, columnspan=2, pady=2)
        ttk.Button(grupo_datos, text="Limpiar Grafo", command=self._limpiar_grafo).grid(row=6, column=0, columnspan=2, pady=2)
        
        # Lista de aristas ingresadas
        ttk.Label(grupo_datos, text="Aristas ingresadas:").grid(row=7, column=0, columnspan=2, sticky=tk.W, pady=(10, 2))
        self.lista_aristas = tk.Listbox(grupo_datos, height=4, width=25)
        self.lista_aristas.grid(row=8, column=0, columnspan=2, pady=2)
        
        # === SECCIÓN: BÚSQUEDA INFORMADA ===
        grupo_busqueda = ttk.LabelFrame(frame_izquierdo, text="🧭 Búsqueda Informada (Hill Climbing)", padding=10)
        grupo_busqueda.pack(fill=tk.X, pady=(0, 10))
        
        ttk.Label(grupo_busqueda, text="Nodo Inicial:").grid(row=0, column=0, sticky=tk.W, pady=2)
        self.entry_inicio = ttk.Entry(grupo_busqueda, width=10)
        self.entry_inicio.grid(row=0, column=1, padx=5, pady=2)
        
        ttk.Label(grupo_busqueda, text="Nodo Final:").grid(row=1, column=0, sticky=tk.W, pady=2)
        self.entry_final = ttk.Entry(grupo_busqueda, width=10)
        self.entry_final.grid(row=1, column=1, padx=5, pady=2)
        
        ttk.Button(grupo_busqueda, text="🎯 Buscar Camino Óptimo", command=self._iniciar_busqueda).grid(row=2, column=0, columnspan=2, pady=5)
        
        # Explicación de búsqueda informada
        explicacion = ttk.Label(grupo_busqueda, text="💡 Hill Climbing busca el camino\nde MENOR COSTO usando heurísticas", 
                               font=("Arial", 8), foreground="blue")
        explicacion.grid(row=3, column=0, columnspan=2, pady=5)
        
        # === SECCIÓN: CONTROL DE ANIMACIÓN ===
        grupo_animacion = ttk.LabelFrame(frame_izquierdo, text="🎬 Control de Animación", padding=10)
        grupo_animacion.pack(fill=tk.X, pady=(0, 10))
        
        ttk.Button(grupo_animacion, text="▶ Iniciar Animación", command=self._iniciar_animacion).pack(fill=tk.X, pady=2)
        ttk.Button(grupo_animacion, text="⏸ Pausar", command=self._pausar_animacion).pack(fill=tk.X, pady=2)
        ttk.Button(grupo_animacion, text="⏹ Reiniciar", command=self._reiniciar_animacion).pack(fill=tk.X, pady=2)
        
        # Control de velocidad
        ttk.Label(grupo_animacion, text="Velocidad (segundos):").pack(pady=(10, 2))
        self.velocidad = tk.DoubleVar(value=1.0)
        scale_velocidad = ttk.Scale(grupo_animacion, from_=0.2, to=3.0, variable=self.velocidad, orient=tk.HORIZONTAL)
        scale_velocidad.pack(fill=tk.X, pady=2)
        
        # === SECCIÓN: INFORMACIÓN ===
        grupo_info = ttk.LabelFrame(frame_izquierdo, text="📈 Información del Proceso", padding=10)
        grupo_info.pack(fill=tk.BOTH, expand=True)
        
        self.texto_info = scrolledtext.ScrolledText(grupo_info, height=12, width=35)
        self.texto_info.pack(fill=tk.BOTH, expand=True)
        
        # === SECCIÓN: VISUALIZACIÓN ===
        grupo_visual = ttk.LabelFrame(frame_derecho, text="🎯 Visualización del Grafo y Búsqueda Informada", padding=10)
        grupo_visual.pack(fill=tk.BOTH, expand=True)
        
        # Canvas para dibujar el grafo
        self.canvas = tk.Canvas(grupo_visual, width=700, height=600, bg='white', relief=tk.SUNKEN, borderwidth=2)
        self.canvas.pack(fill=tk.BOTH, expand=True)
        
        # Leyenda de colores
        frame_leyenda = ttk.Frame(grupo_visual)
        frame_leyenda.pack(fill=tk.X, pady=(5, 0))
        
        colores = [
            ("🟢 Inicial", "#4CAF50"),
            ("🔴 Final", "#F44336"),
            ("🟡 Evaluando", "#FFEB3B"),
            ("🔵 Visitado", "#2196F3"),
            ("🟣 Camino Óptimo", "#9C27B0"),
            ("🟠 Actual", "#FF9800")
        ]
        
        for i, (texto, color) in enumerate(colores):
            frame_color = tk.Frame(frame_leyenda, width=15, height=15, bg=color, relief=tk.RAISED, borderwidth=1)
            frame_color.pack(side=tk.LEFT, padx=2)
            ttk.Label(frame_leyenda, text=texto, font=("Arial", 8)).pack(side=tk.LEFT, padx=(0, 10))
    
    def _mostrar_formato_json(self):
        """Muestra información sobre el formato JSON esperado."""
        formato_info = """
FORMATO JSON PARA BÚSQUEDA INFORMADA:

{
    "nodos": ["A", "B", "C", "D"],
    "aristas": [
        {"origen": "A", "destino": "B", "peso": 1.5},
        {"origen": "B", "destino": "C", "peso": 2.0},
        {"origen": "A", "destino": "D", "peso": 1.0}
    ],
    "posiciones": {
        "A": {"x": 100, "y": 150},
        "B": {"x": 200, "y": 100}
    }
}

CARACTERÍSTICAS DE HILL CLIMBING:
• Búsqueda INFORMADA que SÍ considera pesos/distancias
• Utiliza función de evaluación f(n) = g(n) + h(n)
• g(n) = costo del camino actual
• h(n) = heurística (estimación al objetivo)
• Busca el camino de MENOR COSTO total
• Puede quedar atrapado en óptimos locales
• Más eficiente que búsqueda exhaustiva

DIFERENCIAS CLAVE:
• Búsqueda Ciega (BFS): Ignora costos, encuentra cualquier camino
• Búsqueda Informada (Hill Climbing): Usa costos y heurísticas, busca camino óptimo

VENTAJAS DE HILL CLIMBING:
• Rápido para problemas con buena función heurística
• Usa menos memoria que otros algoritmos informados
• Bueno para optimización local
        """
        
        ventana_formato = tk.Toplevel(self.ventana)
        ventana_formato.title("Formato JSON - Búsqueda Informada")
        ventana_formato.geometry("650x500")
        ventana_formato.transient(self.ventana)
        ventana_formato.grab_set()
        
        texto_formato = scrolledtext.ScrolledText(ventana_formato, wrap=tk.WORD)
        texto_formato.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        texto_formato.insert(tk.END, formato_info)
        texto_formato.config(state=tk.DISABLED)
    
    def _cargar_json(self):
        """Carga un grafo desde un archivo JSON."""
        archivo = filedialog.askopenfilename(
            title="Seleccionar archivo JSON",
            filetypes=[("Archivos JSON", "*.json"), ("Todos los archivos", "*.*")]
        )
        
        if not archivo:
            return
        
        try:
            with open(archivo, 'r', encoding='utf-8') as f:
                datos_json = json.load(f)
            
            # Cargar el grafo
            aristas_cargadas, errores = self.grafo.cargar_desde_json(datos_json)
            
            if aristas_cargadas > 0:
                # Actualizar la lista visual
                self._actualizar_lista_aristas()
                
                # Actualizar visualización
                self._dibujar_grafo()
                
                # Mostrar información de carga
                info_carga = f"✅ ARCHIVO CARGADO EXITOSAMENTE\n"
                info_carga += f"📄 Archivo: {archivo.split('/')[-1]}\n"
                info_carga += f"📊 Aristas cargadas: {aristas_cargadas}\n"
                info_carga += f"📍 Nodos: {len(self.grafo.nodos)} ({', '.join(sorted(self.grafo.nodos))})\n"
                info_carga += f"✅ LISTO para búsqueda INFORMADA (Hill Climbing)\n"
                info_carga += f"🎯 Los pesos SÍ se usan para encontrar el camino óptimo\n"
                
                if errores:
                    info_carga += f"\n⚠️ ERRORES ENCONTRADOS ({len(errores)}):\n"
                    for error in errores[:3]:  # Mostrar solo los primeros 3 errores
                        info_carga += f"• {error}\n"
                    if len(errores) > 3:
                        info_carga += f"• ... y {len(errores) - 3} errores más\n"
                
                self._agregar_info(info_carga)
                
                # Mostrar resumen en messagebox
                mensaje = f"Grafo cargado exitosamente!\n\nAristas: {aristas_cargadas}\nNodos: {len(self.grafo.nodos)}"
                mensaje += f"\n\n✅ Listo para Hill Climbing"
                mensaje += f"\n(Búsqueda INFORMADA con optimización)"
                if errores:
                    mensaje += f"\nErrores: {len(errores)} (ver detalles en el panel)"
                
                messagebox.showinfo("Carga Exitosa", mensaje)
                
            else:
                messagebox.showerror("Error", "No se pudieron cargar aristas válidas del archivo")
                
        except FileNotFoundError:
            messagebox.showerror("Error", "No se pudo encontrar el archivo")
        except ValueError as e:
            messagebox.showerror("Error de Formato", str(e))
        except Exception as e:
            messagebox.showerror("Error", f"Error al cargar archivo: {str(e)}")
    
    def _exportar_json(self):
        """Exporta el grafo actual a un archivo JSON."""
        if not self.grafo.aristas:
            messagebox.showwarning("Advertencia", "No hay datos del grafo para exportar")
            return
        
        archivo = filedialog.asksaveasfilename(
            title="Guardar grafo como JSON",
            defaultextension=".json",
            filetypes=[("Archivos JSON", "*.json"), ("Todos los archivos", "*.*")]
        )
        
        if not archivo:
            return
        
        try:
            datos_json = self.grafo.exportar_a_json()
            
            with open(archivo, 'w', encoding='utf-8') as f:
                json.dump(datos_json, f, indent=2, ensure_ascii=False)
            
            info_exportar = f"💾 GRAFO EXPORTADO EXITOSAMENTE\n"
            info_exportar += f"📄 Archivo: {archivo.split('/')[-1]}\n"
            info_exportar += f"📊 Aristas exportadas: {len(datos_json['aristas'])}\n"
            info_exportar += f"📍 Nodos exportados: {len(datos_json['nodos'])}\n"
            
            self._agregar_info(info_exportar)
            messagebox.showinfo("Exportación Exitosa", f"Grafo guardado en:\n{archivo}")
            
        except Exception as e:
            messagebox.showerror("Error", f"Error al guardar archivo: {str(e)}")
    
    def _actualizar_lista_aristas(self):
        """Actualiza la lista visual de aristas."""
        self.lista_aristas.delete(0, tk.END)
        for origen, destino, peso in self.grafo.aristas:
            self.lista_aristas.insert(tk.END, f"{origen} → {destino} ({peso})")
    
    def _configurar_canvas(self):
        """Configura el canvas y sus propiedades."""
        self.posiciones_nodos = {}  # Almacena las posiciones (x, y) de cada nodo
        self.elementos_canvas = {}  # Almacena los IDs de elementos dibujados
    
    def _agregar_arista(self):
        """Agrega una nueva arista al grafo."""
        origen = self.entry_origen.get().strip().upper()
        destino = self.entry_destino.get().strip().upper()
        peso = self.entry_peso.get().strip()
        
        if not origen or not destino or not peso:
            messagebox.showwarning("Advertencia", "Por favor, complete todos los campos")
            return
        
        if self.grafo.agregar_arista(origen, destino, peso):
            # Agregar a la lista visual
            self.lista_aristas.insert(tk.END, f"{origen} → {destino} ({peso})")
            
            # Limpiar campos
            self.entry_origen.delete(0, tk.END)
            self.entry_destino.delete(0, tk.END)
            self.entry_peso.delete(0, tk.END)
            
            # Actualizar visualización
            self._dibujar_grafo()
            
            self._agregar_info(f"✅ Arista agregada: {origen} → {destino} (peso: {peso})")
            self._agregar_info(f"   🎯 Hill Climbing SÍ usa el peso para optimización")
        else:
            messagebox.showerror("Error", "El peso debe ser un número válido")
    
    def _finalizar_ingreso(self):
        """Finaliza el ingreso de datos y muestra resumen."""
        if not self.grafo.aristas:
            messagebox.showwarning("Advertencia", "No se han ingresado aristas")
            return
        
        resumen = f"""
📊 RESUMEN DEL GRAFO:
• Nodos: {len(self.grafo.nodos)} ({', '.join(sorted(self.grafo.nodos))})
• Aristas: {len(self.grafo.aristas)}
• Tipo: Búsqueda INFORMADA (Hill Climbing)
• Listo para optimización

✅ IMPORTANTE: Hill Climbing SÍ optimiza por distancia
   Encuentra el camino de MENOR COSTO usando heurísticas
        """
        
        self._agregar_info(resumen)
        messagebox.showinfo("Ingreso Finalizado", f"Grafo creado exitosamente!\n\nNodos: {len(self.grafo.nodos)}\nAristas: {len(self.grafo.aristas)}\n\n✅ Listo para Hill Climbing\n(Búsqueda INFORMADA)")
    
    def _limpiar_grafo(self):
        """Limpia todos los datos del grafo."""
        self.grafo.limpiar()
        self.lista_aristas.delete(0, tk.END)
        self.canvas.delete("all")
        self.texto_info.delete(1.0, tk.END)
        self.posiciones_nodos.clear()
        self.elementos_canvas.clear()
        self.pasos_busqueda.clear()
        
        self._agregar_info("🗑 Grafo limpiado")
    
    def _iniciar_busqueda(self):
        """Inicia el proceso de búsqueda INFORMADA Hill Climbing."""
        inicio = self.entry_inicio.get().strip().upper()
        final = self.entry_final.get().strip().upper()
        
        if not inicio or not final:
            messagebox.showwarning("Advertencia", "Ingrese nodo inicial y final")
            return
        
        if not self.grafo.aristas:
            messagebox.showwarning("Advertencia", "Primero debe crear un grafo")
            return
        
        self._agregar_info(f"\n🧭 INICIANDO BÚSQUEDA INFORMADA (Hill Climbing): {inicio} → {final}")
        self._agregar_info("=" * 50)
        self._agregar_info("✅ BÚSQUEDA INFORMADA: SÍ considera pesos/distancias")
        self._agregar_info("🎯 Objetivo: Encontrar el camino de MENOR COSTO")
        self._agregar_info("🧠 Usa heurísticas para guiar la búsqueda")
        
        # Ejecutar Hill Climbing INFORMADO
        camino, pasos = self.algoritmo_hill.buscar_camino(inicio, final, self.posiciones_nodos)
        self.pasos_busqueda = pasos
        self.paso_actual_animacion = 0
        
        if camino:
            costo_total = self._calcular_costo_camino(camino)
            self._agregar_info(f"✅ CAMINO ÓPTIMO ENCONTRADO: {' → '.join(camino)}")
            self._agregar_info(f"💰 Costo total optimizado: {costo_total:.1f}")
            self._agregar_info(f"📊 Número de saltos: {len(camino) - 1}")
            self._agregar_info(f"🔄 Pasos de búsqueda ejecutados: {len(pasos)}")
            self._agregar_info(f"👁️ Nodos evaluados: {len([p for p in pasos if 'evaluaciones' in p])}")
            
            # Mostrar detalles del camino optimizado
            info_detalle = self._obtener_info_detalle_camino(camino)
            if info_detalle:
                self._agregar_info(f"\n📋 Detalle del camino optimizado:")
                self._agregar_info(info_detalle)
            
            # Mostrar el camino final resaltado en el canvas
            self._dibujar_grafo(camino)
        else:
            self._agregar_info("❌ NO SE ENCONTRÓ CAMINO ÓPTIMO")
            self._agregar_info("🔍 Hill Climbing puede quedarse en óptimo local")
            self._agregar_info("💡 Pruebe con otros algoritmos informados (A*)")
        
        self._agregar_info("\n🎬 Use los controles de animación para ver el proceso paso a paso")
    
    def _calcular_costo_camino(self, camino):
        """Calcula el costo total de un camino."""
        if len(camino) < 2:
            return 0
        
        costo_total = 0
        for i in range(len(camino) - 1):
            peso = self.grafo.obtener_peso(camino[i], camino[i + 1])
            if peso is not None:
                costo_total += peso
        
        return costo_total
    
    def _obtener_info_detalle_camino(self, camino):
        """Obtiene información detallada del camino encontrado."""
        if len(camino) < 2:
            return None
        
        info_detalle = []
        costo_acumulado = 0
        
        for i in range(len(camino) - 1):
            peso = self.grafo.obtener_peso(camino[i], camino[i + 1])
            if peso is not None:
                costo_acumulado += peso
                info_detalle.append(f"    {camino[i]} → {camino[i + 1]}: {peso} (acumulado: {costo_acumulado:.1f})")
        
        return "\n".join(info_detalle)
    
    def _iniciar_animacion(self):
        """Inicia la animación del proceso de búsqueda."""
        if not self.pasos_busqueda:
            messagebox.showwarning("Advertencia", "Primero debe realizar una búsqueda")
            return
        
        self.animacion_activa = True
        self.paso_actual_animacion = 0
        
        # Ejecutar animación en hilo separado
        thread_animacion = threading.Thread(target=self._ejecutar_animacion)
        thread_animacion.daemon = True
        thread_animacion.start()
    
    def _pausar_animacion(self):
        """Pausa la animación actual."""
        self.animacion_activa = False
    
    def _reiniciar_animacion(self):
        """Reinicia la animación desde el principio."""
        self.animacion_activa = False
        self.paso_actual_animacion = 0
        self._dibujar_grafo()  # Resetear visualización sin camino resaltado
    
    def _ejecutar_animacion(self):
        """Ejecuta la animación paso a paso."""
        while self.animacion_activa and self.paso_actual_animacion < len(self.pasos_busqueda):
            paso = self.pasos_busqueda[self.paso_actual_animacion]
            
            # Actualizar visualización en el hilo principal
            self.ventana.after(0, self._actualizar_paso_animacion, paso)
            
            # Esperar según la velocidad configurada
            time.sleep(self.velocidad.get())
            
            self.paso_actual_animacion += 1
        
        # Animación completada
        if self.paso_actual_animacion >= len(self.pasos_busqueda):
            self.ventana.after(0, self._animacion_completada)
    
    def _actualizar_paso_animacion(self, paso):
        """Actualiza la visualización para un paso específico de la animación."""
        # Determinar si hay camino final
        camino_final = paso.get('camino_final', None)
        
        # Redibujar grafo base
        self._dibujar_grafo(camino_final)
        
        # Resaltar nodos según el estado actual
        if not camino_final:
            for nodo in self.grafo.nodos:
                color = "lightgray"
                
                if nodo == paso.get('nodo_actual'):
                    color = "#FF9800"  # Naranja - nodo actual
                elif nodo in paso.get('visitados', set()):
                    color = "#2196F3"  # Azul - visitado
                
                self._colorear_nodo(nodo, color)
            
            # Resaltar evaluaciones si existen
            if 'evaluaciones' in paso:
                for eval_info in paso['evaluaciones']:
                    self._colorear_nodo(eval_info['vecino'], "#FFEB3B")  # Amarillo - evaluando
        
        # Actualizar información del paso
        info = f"PASO {paso['paso']}: {paso['accion']}\n"
        if 'camino_actual' in paso:
            info += f"Camino actual: {' → '.join(paso['camino_actual'])}\n"
        if 'costo_total' in paso:
            info += f"Costo acumulado: {paso['costo_total']:.1f}\n"
        if 'evaluaciones' in paso:
            info += "Evaluaciones: " + ", ".join([
                f"{ev['vecino']}(f={ev['evaluacion']:.1f})" 
                for ev in paso['evaluaciones']
            ]) + "\n"
        
        self.texto_info.insert(tk.END, info + "\n")
        self.texto_info.see(tk.END)
    
    def _animacion_completada(self):
        """Se ejecuta cuando la animación termina."""
        self.animacion_activa = False
        self._agregar_info("\n🎊 ANIMACIÓN DE BÚSQUEDA INFORMADA COMPLETADA")
    
    def _dibujar_grafo(self, camino_final=None):
        """Dibuja el grafo en el canvas."""
        self.canvas.delete("all")
        
        if not self.grafo.nodos:
            return
        
        # Calcular posiciones de nodos si no existen
        if not self.posiciones_nodos or set(self.posiciones_nodos.keys()) != self.grafo.nodos:
            self._calcular_posiciones_nodos()
        
        # Crear conjunto de aristas del camino final para búsqueda rápida
        aristas_camino = set()
        if camino_final:
            for i in range(len(camino_final) - 1):
                aristas_camino.add((camino_final[i], camino_final[i + 1]))
        
        # Detectar aristas bidireccionales para aplicar offset
        aristas_procesadas = set()
        aristas_bidireccionales = set()
        
        for origen, destino, peso in self.grafo.aristas:
            par_nodos = tuple(sorted([origen, destino]))
            if par_nodos in aristas_procesadas:
                aristas_bidireccionales.add(par_nodos)
            else:
                aristas_procesadas.add(par_nodos)
        
        # Dibujar aristas con offset apropiado
        offset_aplicado = {}
        
        for origen, destino, peso in self.grafo.aristas:
            es_camino = (origen, destino) in aristas_camino
            par_nodos = tuple(sorted([origen, destino]))
            
            # Determinar offset para aristas bidireccionales
            offset_curva = 0
            if par_nodos in aristas_bidireccionales:
                # Crear clave única para la dirección específica
                direccion_key = f"{origen}->{destino}"
                
                if par_nodos not in offset_aplicado:
                    offset_aplicado[par_nodos] = {}
                
                if direccion_key not in offset_aplicado[par_nodos]:
                    # Asignar offset según la dirección
                    num_direcciones = len(offset_aplicado[par_nodos])
                    if num_direcciones == 0:
                        offset_curva = -30  # Primera dirección: curva hacia un lado
                    else:
                        offset_curva = 30   # Segunda dirección: curva hacia el otro lado
                    
                    offset_aplicado[par_nodos][direccion_key] = offset_curva
                else:
                    offset_curva = offset_aplicado[par_nodos][direccion_key]
            
            self._dibujar_arista(origen, destino, peso, es_camino, offset_curva)
        
        # Dibujar nodos encima de las aristas
        for nodo in self.grafo.nodos:
            color_nodo = "lightblue"
            if camino_final and nodo in camino_final:
                if nodo == camino_final[0]:
                    color_nodo = "#4CAF50"  # Verde para inicio
                elif nodo == camino_final[-1]:
                    color_nodo = "#F44336"  # Rojo para final
                else:
                    color_nodo = "#9C27B0"  # Morado para camino
            
            self._dibujar_nodo(nodo, color_nodo)
    
    def _calcular_posiciones_nodos(self):
        """Calcula posiciones para los nodos usando un layout circular."""
        self.posiciones_nodos.clear()
        
        nodos = list(self.grafo.nodos)
        n = len(nodos)
        
        if n == 0:
            return
        
        # Centro del canvas
        centro_x = 350
        centro_y = 300
        radio = min(250, 200)  # Radio del círculo
        
        if n == 1:
            self.posiciones_nodos[nodos[0]] = (centro_x, centro_y)
        else:
            for i, nodo in enumerate(nodos):
                angulo = 2 * math.pi * i / n
                x = centro_x + radio * math.cos(angulo)
                y = centro_y + radio * math.sin(angulo)
                self.posiciones_nodos[nodo] = (x, y)
    
    def _dibujar_nodo(self, nodo, color="lightblue"):
        """Dibuja un nodo en el canvas."""
        if nodo not in self.posiciones_nodos:
            return
        
        x, y = self.posiciones_nodos[nodo]
        radio = 25
        
        # Dibujar círculo del nodo
        circulo = self.canvas.create_oval(
            x - radio, y - radio, x + radio, y + radio,
            fill=color, outline="black", width=2
        )
        
        # Dibujar etiqueta del nodo
        texto = self.canvas.create_text(
            x, y, text=str(nodo), font=("Arial", 12, "bold"), fill="black"
        )
        
        self.elementos_canvas[f"nodo_{nodo}"] = [circulo, texto]
    
    def _colorear_nodo(self, nodo, color):
        """Cambia el color de un nodo específico."""
        if f"nodo_{nodo}" in self.elementos_canvas:
            circulo_id = self.elementos_canvas[f"nodo_{nodo}"][0]
            self.canvas.itemconfig(circulo_id, fill=color)
    
    def _dibujar_arista(self, origen, destino, peso, es_camino_final=False, offset_curva=0):
        """Dibuja una arista entre dos nodos con posible curvatura para evitar superposición."""
        if origen not in self.posiciones_nodos or destino not in self.posiciones_nodos:
            return
        
        x1, y1 = self.posiciones_nodos[origen]
        x2, y2 = self.posiciones_nodos[destino]
        
        # Configurar estilo según si es parte del camino final
        if es_camino_final:
            color_linea = "#9C27B0"  # Morado para camino final
            grosor_linea = 5  # Más gruesa
            forma_flecha = (20, 25, 8)  # Flecha más grande
        else:
            color_linea = "darkblue"  # Azul normal
            grosor_linea = 3  # Un poco más gruesa para mejor visibilidad
            forma_flecha = (18, 22, 7)  # Flecha más visible
        
        # Si hay offset, crear una curva para separar aristas bidireccionales
        if offset_curva != 0:
            # Calcular punto de control para la curva
            mid_x = (x1 + x2) / 2
            mid_y = (y1 + y2) / 2
            
            # Vector perpendicular para el offset
            dx = x2 - x1
            dy = y2 - y1
            length = math.sqrt(dx*dx + dy*dy)
            
            if length > 0:
                # Vector perpendicular normalizado
                perp_x = -dy / length * offset_curva
                perp_y = dx / length * offset_curva
                
                # Punto de control para la curva
                control_x = mid_x + perp_x
                control_y = mid_y + perp_y
                
                # Dibujar línea curva usando múltiples segmentos
                puntos = self._generar_curva_bezier(x1, y1, control_x, control_y, x2, y2, 20)
                
                # Dibujar la curva
                linea = self.canvas.create_line(
                    puntos,
                    fill=color_linea, 
                    width=grosor_linea,
                    capstyle=tk.ROUND,
                    smooth=True
                )
                
                # Calcular posición y ángulo para la flecha
                # Usar los últimos dos puntos para determinar la dirección
                p1_x, p1_y = puntos[-4], puntos[-3]
                p2_x, p2_y = puntos[-2], puntos[-1]
                
                # Dibujar flecha separada al final de la curva
                self._dibujar_flecha_direccional(p1_x, p1_y, p2_x, p2_y, color_linea, forma_flecha)
                
            else:
                # Fallback a línea recta si no se puede calcular
                linea = self._dibujar_linea_recta(x1, y1, x2, y2, color_linea, grosor_linea, forma_flecha)
        else:
            # Línea recta normal
            linea = self._dibujar_linea_recta(x1, y1, x2, y2, color_linea, grosor_linea, forma_flecha)
        
        # Calcular posición para la etiqueta del peso
        if offset_curva != 0:
            # Para curvas, poner la etiqueta en el punto de máxima curvatura
            mid_x = (x1 + x2) / 2
            mid_y = (y1 + y2) / 2
            dx = x2 - x1
            dy = y2 - y1
            length = math.sqrt(dx*dx + dy*dy)
            
            if length > 0:
                perp_x = -dy / length * (offset_curva + 15)
                perp_y = dx / length * (offset_curva + 15)
                label_x = mid_x + perp_x
                label_y = mid_y + perp_y
            else:
                label_x, label_y = mid_x, mid_y
        else:
            # Para líneas rectas
            label_x = (x1 + x2) / 2
            label_y = (y1 + y2) / 2
            
            # Desplazar ligeramente para evitar superposición
            dx = x2 - x1
            dy = y2 - y1
            length = math.sqrt(dx*dx + dy*dy)
            if length > 0:
                perp_x = -dy / length * 20
                perp_y = dx / length * 20
                label_x += perp_x
                label_y += perp_y
        
        # Crear fondo para la etiqueta del peso
        bbox_padding = 12
        etiqueta_bg = self.canvas.create_oval(
            label_x - bbox_padding, label_y - bbox_padding,
            label_x + bbox_padding, label_y + bbox_padding,
            fill="white", outline="gray", width=1
        )
        
        # Dibujar etiqueta del peso (IMPORTANTE para optimización)
        color_texto = "#9C27B0" if es_camino_final else "red"
        etiqueta = self.canvas.create_text(
            label_x, label_y, text=str(peso),
            font=("Arial", 10, "bold"), fill=color_texto
        )
        
        # Usar ID único para cada arista direccional
        arista_id = f"arista_{origen}_{destino}_{abs(hash(f'{origen}{destino}{peso}{offset_curva}')) % 10000}"
        self.elementos_canvas[arista_id] = [linea, etiqueta_bg, etiqueta]
    
    def _generar_curva_bezier(self, x1, y1, cx, cy, x2, y2, segments):
        """Genera puntos para una curva de Bézier cuadrática."""
        puntos = []
        for i in range(segments + 1):
            t = i / segments
            # Fórmula de Bézier cuadrática
            x = (1-t)**2 * x1 + 2*(1-t)*t * cx + t**2 * x2
            y = (1-t)**2 * y1 + 2*(1-t)*t * cy + t**2 * y2
            puntos.extend([x, y])
        return puntos
    
    def _dibujar_linea_recta(self, x1, y1, x2, y2, color, grosor, forma_flecha):
        """Dibuja una línea recta con flecha."""
        return self.canvas.create_line(
            x1, y1, x2, y2, 
            arrow=tk.LAST, 
            arrowshape=forma_flecha,
            fill=color, 
            width=grosor,
            capstyle=tk.ROUND,
            smooth=True
        )
    
    def _dibujar_flecha_direccional(self, x1, y1, x2, y2, color, forma_flecha):
        """Dibuja una flecha direccional independiente."""
        # Calcular el vector direccional
        dx = x2 - x1
        dy = y2 - y1
        length = math.sqrt(dx*dx + dy*dy)
        
        if length > 0:
            # Normalizar
            dx /= length
            dy /= length
            
            # Crear puntos para la flecha
            arrow_length = forma_flecha[1]
            arrow_width = forma_flecha[2]
            
            # Punto base de la flecha
            base_x = x2 - dx * arrow_length
            base_y = y2 - dy * arrow_length
            
            # Puntos laterales
            perp_x = -dy * arrow_width
            perp_y = dx * arrow_width
            
            left_x = base_x + perp_x
            left_y = base_y + perp_y
            right_x = base_x - perp_x
            right_y = base_y - perp_y
            
            # Dibujar el triángulo de la flecha
            self.canvas.create_polygon(
                x2, y2, left_x, left_y, right_x, right_y,
                fill=color, outline=color, width=1
            )
    
    def _agregar_info(self, texto):
        """Agrega texto al área de información."""
        self.texto_info.insert(tk.END, texto + "\n")
        self.texto_info.see(tk.END)
    
    def ejecutar(self):
        """Inicia la aplicación."""
        # Mensaje de bienvenida
        bienvenida = """
🎓 BÚSQUEDA INFORMADA - ALGORITMO HILL CLIMBING
===============================================

✅ IMPORTANTE: BÚSQUEDA INFORMADA
• SÍ considera pesos/distancias para optimización
• Usa heurísticas para guiar la búsqueda hacia el objetivo
• Encuentra caminos de MENOR COSTO (no solo cualquier camino)
• Más eficiente que búsqueda exhaustiva

📋 INSTRUCCIONES:

📁 OPCIÓN 1 - CARGAR ARCHIVO JSON:
• Use "Cargar Grafo desde JSON" para importar un grafo
• Vea el formato requerido con "Ver Formato JSON"
• Especifique nodos inicial y final para la búsqueda

📊 OPCIÓN 2 - ENTRADA MANUAL:
• Agregue aristas ingresando nodo salida, entrada y distancia
• Haga clic en "Finalizar Ingreso" cuando termine
• Especifique nodos inicial y final para la búsqueda

🧭 BÚSQUEDA INFORMADA:
• Presione "Buscar Camino Óptimo" para ejecutar Hill Climbing
• Use los controles de animación para visualizar el proceso
• Hill Climbing busca el camino de MENOR COSTO usando heurísticas

💾 EXPORTAR:
• Use "Exportar Grafo a JSON" para guardar su trabajo

🎯 DIFERENCIA CLAVE CON BÚSQUEDA CIEGA:
• Búsqueda Ciega: Encuentra cualquier camino válido
• Búsqueda Informada: Encuentra el camino ÓPTIMO (menor costo)

¡Comience creando su grafo para búsqueda informada! 🚀
        """
        
        self.texto_info.insert(tk.END, bienvenida)
        
        # Iniciar loop principal
        self.ventana.mainloop()

def main():
    """Función principal del programa."""
    print("🚀 Iniciando aplicación de Búsqueda Informada (Hill Climbing)...")
    print("✅ RECORDATORIO: Búsqueda informada SÍ optimiza por distancia")
    print("📊 Cargando interfaz gráfica...")
    
    try:
        app = InterfazGrafica()
        app.ejecutar()
    except KeyboardInterrupt:
        print("\n👋 Aplicación cerrada por el usuario")
    except Exception as e:
        print(f"❌ Error al ejecutar la aplicación: {e}")
    finally:
        print("🏁 Programa finalizado")

if __name__ == "__main__":
    main()
        
