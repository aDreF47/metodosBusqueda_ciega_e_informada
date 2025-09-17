"""
PROYECTO: Búsqueda Ciega - Algoritmo BFS Puro con Interfaz Gráfica
Autor: Fernando Celadita
Descripción: Implementación de búsqueda ciega en amplitud (BFS) con GUI interactiva
para visualizar el proceso de búsqueda en grafos direccionados.
NOTA: Búsqueda ciega NO considera pesos para encontrar caminos óptimos.
"""

import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext, filedialog
import time
import threading
from collections import deque, defaultdict
import math
import json

class Grafo:
    """
    Clase que representa un grafo direccionado con pesos en las aristas.
    Para búsqueda ciega, los pesos se almacenan solo para visualización,
    NO se usan en el algoritmo de búsqueda.
    """
    
    def __init__(self):
        self.adyacencias = defaultdict(list)  # Lista de adyacencia
        self.aristas = []  # Lista de todas las aristas (origen, destino, peso)
        self.nodos = set()  # Conjunto de todos los nodos
    
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
    
    def obtener_vecinos(self, nodo):
        """
        Retorna SOLO los nodos vecinos de un nodo dado.
        Para búsqueda ciega, NO retorna los pesos.
        """
        return [destino for destino, _ in self.adyacencias[nodo]]
    
    def obtener_peso(self, origen, destino):
        """
        Obtiene el peso de la arista entre dos nodos.
        Solo se usa para visualización del grafo.
        """
        for dest, peso in self.adyacencias[origen]:
            if dest == destino:
                return peso
        return None
    
    def cargar_desde_json(self, datos_json):
        """
        Carga el grafo desde datos JSON.
        Formato esperado:
        {
            "nodos": ["A", "B", "C"],
            "aristas": [
                {"origen": "A", "destino": "B", "peso": 1.5},
                {"origen": "B", "destino": "C", "peso": 2.0}
            ]
        }
        """
        try:
            # Limpiar grafo actual
            self.limpiar()
            
            # Validar estructura básica
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
            
            return aristas_cargadas, errores
            
        except json.JSONDecodeError as e:
            raise ValueError(f"Archivo JSON inválido: {str(e)}")
        except Exception as e:
            raise ValueError(f"Error al procesar el archivo: {str(e)}")
    
    def exportar_a_json(self):
        """Exporta el grafo actual a formato JSON."""
        datos = {
            "nodos": list(self.nodos),
            "aristas": []
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

class AlgoritmoBFS:
    """
    Implementación PURA del algoritmo de Búsqueda Ciega en Amplitud (BFS).
    NO considera pesos ni distancias, solo encuentra UN camino válido.
    """
    
    def __init__(self, grafo):
        self.grafo = grafo
        self.cola = deque()
        self.visitados = set()
        self.padre = {}
        self.paso_actual = 0
        self.pasos_busqueda = []
    
    def buscar_camino(self, inicio, final):
        """
        Ejecuta BFS CIEGA para encontrar UN camino del nodo inicial al final.
        NO optimiza por distancia, solo encuentra el primer camino válido.
        Retorna: (camino_encontrado, lista_de_pasos_detallados)
        """
        # Reiniciar estado
        self.cola.clear()
        self.visitados.clear()
        self.padre.clear()
        self.pasos_busqueda.clear()
        self.paso_actual = 0
        
        # Verificar que los nodos existen en el grafo
        if inicio not in self.grafo.nodos or final not in self.grafo.nodos:
            return None, ["Error: Uno o ambos nodos no existen en el grafo"]
        
        # Inicializar BFS
        self.cola.append(inicio)
        self.visitados.add(inicio)
        self.padre[inicio] = None
        
        self.pasos_busqueda.append({
            'paso': 0,
            'accion': f'Inicializar: Cola=[{inicio}], Visitados=[{inicio}]',
            'cola': list(self.cola),
            'visitados': set(self.visitados),
            'nodo_actual': inicio
        })
        
        paso = 1
        
        # Ejecutar BFS CIEGA
        while self.cola:
            nodo_actual = self.cola.popleft()
            
            self.pasos_busqueda.append({
                'paso': paso,
                'accion': f'Procesar nodo: {nodo_actual}',
                'cola': list(self.cola),
                'visitados': set(self.visitados),
                'nodo_actual': nodo_actual
            })
            paso += 1
            
            # ¿Encontramos el objetivo?
            if nodo_actual == final:
                camino = self._reconstruir_camino(inicio, final)
                self.pasos_busqueda.append({
                    'paso': paso,
                    'accion': f'¡Meta encontrada! Camino: {" → ".join(camino)}',
                    'cola': list(self.cola),
                    'visitados': set(self.visitados),
                    'nodo_actual': final,
                    'camino_final': camino
                })
                return camino, self.pasos_busqueda
            
            # Explorar vecinos (SIN considerar pesos)
            vecinos = self.grafo.obtener_vecinos(nodo_actual)
            vecinos_nuevos = []
            
            for vecino in vecinos:
                if vecino not in self.visitados:
                    self.cola.append(vecino)
                    self.visitados.add(vecino)
                    self.padre[vecino] = nodo_actual
                    vecinos_nuevos.append(vecino)
            
            if vecinos_nuevos:
                self.pasos_busqueda.append({
                    'paso': paso,
                    'accion': f'Agregar vecinos de {nodo_actual}: {vecinos_nuevos}',
                    'cola': list(self.cola),
                    'visitados': set(self.visitados),
                    'nodo_actual': nodo_actual,
                    'vecinos_agregados': vecinos_nuevos
                })
                paso += 1
        
        # No se encontró camino
        self.pasos_busqueda.append({
            'paso': paso,
            'accion': 'Búsqueda terminada: No existe camino',
            'cola': [],
            'visitados': set(self.visitados),
            'nodo_actual': None
        })
        
        return None, self.pasos_busqueda
    
    def _reconstruir_camino(self, inicio, final):
        """Reconstruye el camino desde el nodo inicial hasta el final."""
        camino = []
        actual = final
        
        while actual is not None:
            camino.append(actual)
            actual = self.padre[actual]
        
        return camino[::-1]  # Invertir para obtener el camino correcto

class InterfazGrafica:
    """
    Interfaz gráfica para búsqueda ciega BFS.
    Muestra el proceso de búsqueda SIN optimización por distancia.
    """
    
    def __init__(self):
        self.ventana = tk.Tk()
        self.ventana.title("Búsqueda Ciega - BFS (Sin optimización de distancia)")
        self.ventana.geometry("1200x800")
        self.ventana.configure(bg='#f0f0f0')
        
        # Datos del programa
        self.grafo = Grafo()
        self.algoritmo_bfs = AlgoritmoBFS(self.grafo)
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
        
        # Nota sobre búsqueda ciega
        nota_label = ttk.Label(grupo_datos, text="⚠️ Nota: Distancia solo para visualización\n(Búsqueda ciega NO la usa)", 
                              font=("Arial", 8), foreground="orange")
        nota_label.grid(row=3, column=0, columnspan=2, pady=5)
        
        # Botones de control de datos
        ttk.Button(grupo_datos, text="Agregar Arista", command=self._agregar_arista).grid(row=4, column=0, columnspan=2, pady=5)
        ttk.Button(grupo_datos, text="Finalizar Ingreso", command=self._finalizar_ingreso).grid(row=5, column=0, columnspan=2, pady=2)
        ttk.Button(grupo_datos, text="Limpiar Grafo", command=self._limpiar_grafo).grid(row=6, column=0, columnspan=2, pady=2)
        
        # Lista de aristas ingresadas
        ttk.Label(grupo_datos, text="Aristas ingresadas:").grid(row=7, column=0, columnspan=2, sticky=tk.W, pady=(10, 2))
        self.lista_aristas = tk.Listbox(grupo_datos, height=4, width=25)
        self.lista_aristas.grid(row=8, column=0, columnspan=2, pady=2)
        
        # === SECCIÓN: BÚSQUEDA CIEGA ===
        grupo_busqueda = ttk.LabelFrame(frame_izquierdo, text="🔍 Búsqueda Ciega (BFS)", padding=10)
        grupo_busqueda.pack(fill=tk.X, pady=(0, 10))
        
        ttk.Label(grupo_busqueda, text="Nodo Inicial:").grid(row=0, column=0, sticky=tk.W, pady=2)
        self.entry_inicio = ttk.Entry(grupo_busqueda, width=10)
        self.entry_inicio.grid(row=0, column=1, padx=5, pady=2)
        
        ttk.Label(grupo_busqueda, text="Nodo Final:").grid(row=1, column=0, sticky=tk.W, pady=2)
        self.entry_final = ttk.Entry(grupo_busqueda, width=10)
        self.entry_final.grid(row=1, column=1, padx=5, pady=2)
        
        ttk.Button(grupo_busqueda, text="🔍 Buscar Camino (BFS)", command=self._iniciar_busqueda).grid(row=2, column=0, columnspan=2, pady=5)
        
        # Explicación de búsqueda ciega
        explicacion = ttk.Label(grupo_busqueda, text="💡 BFS encuentra UN camino válido\n(NO el más corto en distancia)", 
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
        grupo_visual = ttk.LabelFrame(frame_derecho, text="🎯 Visualización del Grafo y Búsqueda Ciega", padding=10)
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
            ("🟡 En Cola", "#FFEB3B"),
            ("🔵 Visitado", "#2196F3"),
            ("🟣 Camino Encontrado", "#9C27B0")
        ]
        
        for i, (texto, color) in enumerate(colores):
            frame_color = tk.Frame(frame_leyenda, width=15, height=15, bg=color, relief=tk.RAISED, borderwidth=1)
            frame_color.pack(side=tk.LEFT, padx=2)
            ttk.Label(frame_leyenda, text=texto, font=("Arial", 8)).pack(side=tk.LEFT, padx=(0, 10))
    
    def _mostrar_formato_json(self):
        """Muestra información sobre el formato JSON esperado."""
        formato_info = """
FORMATO JSON PARA CARGA DE GRAFO:

{
    "nodos": ["A", "B", "C", "D"],
    "aristas": [
        {"origen": "A", "destino": "B", "peso": 1.5},
        {"origen": "B", "destino": "C", "peso": 2.0},
        {"origen": "A", "destino": "D", "peso": 1.0}
    ]
}

NOTAS IMPORTANTES SOBRE BÚSQUEDA CIEGA:
• La sección "nodos" es opcional
• Los pesos se almacenan SOLO para visualización del grafo
• El algoritmo BFS NO usa los pesos para encontrar el camino
• BFS encuentra UN camino válido (no necesariamente el más corto)
• Los nombres de nodos se convertirán a mayúsculas
• Se pueden usar nodos alfanuméricos (A, B1, NODE_1, etc.)

DIFERENCIA CLAVE:
• Búsqueda Ciega: Ignora pesos, encuentra cualquier camino
• Búsqueda Informada: Usa pesos, encuentra camino óptimo
        """
        
        ventana_formato = tk.Toplevel(self.ventana)
        ventana_formato.title("Formato JSON - Búsqueda Ciega")
        ventana_formato.geometry("600x450")
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
                info_carga += f"🔸 Nodos: {len(self.grafo.nodos)} ({', '.join(sorted(self.grafo.nodos))})\n"
                info_carga += f"⚠️ RECORDATORIO: Búsqueda ciega NO usa pesos para optimización\n"
                
                if errores:
                    info_carga += f"\n⚠️ ERRORES ENCONTRADOS ({len(errores)}):\n"
                    for error in errores[:3]:  # Mostrar solo los primeros 3 errores
                        info_carga += f"• {error}\n"
                    if len(errores) > 3:
                        info_carga += f"• ... y {len(errores) - 3} errores más\n"
                
                self._agregar_info(info_carga)
                
                # Mostrar resumen en messagebox
                mensaje = f"Grafo cargado exitosamente!\n\nAristas: {aristas_cargadas}\nNodos: {len(self.grafo.nodos)}"
                mensaje += f"\n\n⚠️ Recordatorio: BFS es búsqueda CIEGA"
                mensaje += f"\n(No optimiza por distancia)"
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
            info_exportar += f"🔸 Nodos exportados: {len(datos_json['nodos'])}\n"
            
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
            self._agregar_info(f"   ⚠️ Nota: BFS NO usa el peso para búsqueda")
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
• Tipo: Búsqueda CIEGA (BFS)
• Listo para búsqueda

⚠️ IMPORTANTE: BFS NO optimiza por distancia
   Solo encuentra UN camino válido
        """
        
        self._agregar_info(resumen)
        messagebox.showinfo("Ingreso Finalizado", f"Grafo creado exitosamente!\n\nNodos: {len(self.grafo.nodos)}\nAristas: {len(self.grafo.aristas)}\n\n⚠️ Recordatorio: Búsqueda CIEGA")
    
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
        """Inicia el proceso de búsqueda CIEGA BFS."""
        inicio = self.entry_inicio.get().strip().upper()
        final = self.entry_final.get().strip().upper()
        
        if not inicio or not final:
            messagebox.showwarning("Advertencia", "Ingrese nodo inicial y final")
            return
        
        if not self.grafo.aristas:
            messagebox.showwarning("Advertencia", "Primero debe crear un grafo")
            return
        
        self._agregar_info(f"\n🔍 INICIANDO BÚSQUEDA CIEGA (BFS): {inicio} → {final}")
        self._agregar_info("=" * 45)
        self._agregar_info("⚠️ BÚSQUEDA CIEGA: NO considera pesos/distancias")
        self._agregar_info("🎯 Objetivo: Encontrar UN camino válido")
        
        # Ejecutar BFS CIEGO
        camino, pasos = self.algoritmo_bfs.buscar_camino(inicio, final)
        self.pasos_busqueda = pasos
        self.paso_actual_animacion = 0
        
        if camino:
            self._agregar_info(f"✅ CAMINO ENCONTRADO: {' → '.join(camino)}")
            self._agregar_info(f"📊 Número de saltos: {len(camino) - 1}")
            self._agregar_info(f"🔄 Pasos de búsqueda ejecutados: {len(pasos)}")
            self._agregar_info(f"👁️ Nodos explorados: {len([p for p in pasos if 'visitados' in p and p['visitados']])}")
            
            # Mostrar información adicional solo para referencia (NO para optimización)
            info_referencia = self._obtener_info_referencia_camino(camino)
            if info_referencia:
                self._agregar_info(f"\n📋 Información de referencia del camino:")
                self._agregar_info(f"    (Solo para visualización, NO usada en búsqueda)")
                self._agregar_info(info_referencia)
            
            # Mostrar el camino final resaltado en el canvas
            self._dibujar_grafo(camino)
        else:
            self._agregar_info("❌ NO SE ENCONTRÓ CAMINO")
            self._agregar_info("🔍 No existe conexión entre los nodos especificados")
        
        self._agregar_info("\n🎬 Use los controles de animación para ver el proceso paso a paso")
    
    def _obtener_info_referencia_camino(self, camino):
        """
        Obtiene información de referencia del camino encontrado.
        IMPORTANTE: Esta información es SOLO para mostrar, NO se usa en la búsqueda.
        """
        if len(camino) < 2:
            return None
        
        distancia_total = 0
        info_detalle = []
        
        for i in range(len(camino) - 1):
            peso = self.grafo.obtener_peso(camino[i], camino[i + 1])
            if peso is not None:
                distancia_total += peso
                info_detalle.append(f"    {camino[i]} → {camino[i + 1]}: {peso}")
        
        info = f"    Distancia total acumulada: {distancia_total:.1f}\n"
        info += "    Detalle por arista:\n" + "\n".join(info_detalle)
        
        return info
    
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
        
        # Resaltar nodos según el estado actual (solo si no hay camino final)
        if not camino_final:
            for nodo in self.grafo.nodos:
                color = "lightgray"
                
                if nodo == paso.get('nodo_actual'):
                    color = "#FFC107"  # Amarillo - procesando
                elif nodo in paso.get('visitados', set()):
                    color = "#2196F3"  # Azul - visitado
                elif nodo in paso.get('cola', []):
                    color = "#FFEB3B"  # Amarillo claro - en cola
                
                self._colorear_nodo(nodo, color)
        
        # Actualizar información del paso
        info = f"PASO {paso['paso']}: {paso['accion']}\n"
        info += f"Cola: {paso.get('cola', [])}\n"
        info += f"Visitados: {list(paso.get('visitados', set()))}\n"
        
        self.texto_info.insert(tk.END, info + "\n")
        self.texto_info.see(tk.END)
    
    def _animacion_completada(self):
        """Se ejecuta cuando la animación termina."""
        self.animacion_activa = False
        self._agregar_info("\n🏁 ANIMACIÓN DE BÚSQUEDA CIEGA COMPLETADA")
    
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
        
        # Dibujar etiqueta del peso (SOLO para visualización)
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
🎓 BÚSQUEDA CIEGA - ALGORITMO BFS PURO
=========================================

⚠️ IMPORTANTE: BÚSQUEDA CIEGA
• NO considera pesos/distancias para tomar decisiones
• Solo encuentra UN camino válido (no el óptimo)
• Los pesos se muestran SOLO para visualización del grafo

📋 INSTRUCCIONES:

📁 OPCIÓN 1 - CARGAR ARCHIVO JSON:
• Use "Cargar Grafo desde JSON" para importar un grafo
• Vea el formato requerido con "Ver Formato JSON"
• Especifique nodos inicial y final para la búsqueda

📊 OPCIÓN 2 - ENTRADA MANUAL:
• Agregue aristas ingresando nodo salida, entrada y distancia
• Haga clic en "Finalizar Ingreso" cuando termine
• Especifique nodos inicial y final para la búsqueda

🔍 BÚSQUEDA CIEGA:
• Presione "Buscar Camino (BFS)" para ejecutar búsqueda ciega
• Use los controles de animación para visualizar el proceso
• BFS encuentra el primer camino válido (menor número de saltos)

💾 EXPORTAR:
• Use "Exportar Grafo a JSON" para guardar su trabajo

¡Recuerde: Esta es búsqueda CIEGA, no optimiza por distancia! 🚀
        """
        
        self.texto_info.insert(tk.END, bienvenida)
        
        # Iniciar loop principal
        self.ventana.mainloop()

def main():
    """Función principal del programa."""
    print("🚀 Iniciando aplicación de Búsqueda Ciega (BFS Puro)...")
    print("⚠️ RECORDATORIO: Búsqueda ciega NO optimiza por distancia")
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
