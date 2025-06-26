import warnings
warnings.filterwarnings("ignore", category=UserWarning)
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import math
import time
import threading
from PIL import Image, ImageTk, ImageOps
import os
import csv
from collections import defaultdict
import random
from datetime import datetime, timedelta
import io
import pygame  # Added for background music


class Planet:
    """Class to represent a planet with its properties and orbital data"""

    def __init__(self, name, radius, distance_from_sun, orbital_speed, color,
                 moons, facts, axial_tilt, orbital_inclination, has_rings=False,
                 image_path=None, mass=None, diameter=None, density=None,
                 gravity=None, escape_velocity=None, rotation_period=None,
                 length_of_day=None, perihelion=None, aphelion=None,
                 orbital_period=None, orbital_velocity=None,
                 orbital_eccentricity=None, obliquity_to_orbit=None,
                 mean_temperature=None, surface_pressure=None,
                 has_ring_system=None, has_global_magnetic_field=None):
        self.name = name
        self.radius = radius  # Scaled radius for visualization
        self.distance_from_sun = distance_from_sun  # Scaled distance
        self.orbital_speed = orbital_speed  # Radians per frame
        self.color = color
        self.moons = moons
        self.facts = facts
        self.axial_tilt = axial_tilt  # Axial tilt in degrees
        self.orbital_inclination = orbital_inclination  # Orbital inclination in degrees
        self.has_rings = has_rings  # Whether the planet has rings

        # Position and orientation
        self.angle = random.uniform(0, 2 * math.pi)  # Random starting position
        self.initial_angle = self.angle  # Store initial angle for reset
        self.x = 0
        self.y = 0
        self.z = 0  # For 3D depth
        self.rotation_angle = 0  # For planet rotation

        # Image handling
        self.image_path = image_path
        self.image = None  # Will store the processed image
        self.photo_image = None  # Will store the PhotoImage for tkinter
        self.texture_image = None  # For 3D texture mapping

        # Scientific properties
        self.mass = mass  # 10^24 kg
        self.diameter = diameter  # km
        self.density = density  # kg/m³
        self.gravity = gravity  # m/s²
        self.escape_velocity = escape_velocity  # km/s
        self.rotation_period = rotation_period  # hours
        self.length_of_day = length_of_day  # hours
        self.perihelion = perihelion  # 10^6 km
        self.aphelion = aphelion  # 10^6 km
        self.orbital_period = orbital_period  # days
        self.orbital_velocity = orbital_velocity  # km/s
        self.orbital_eccentricity = orbital_eccentricity
        self.obliquity_to_orbit = obliquity_to_orbit  # degrees
        self.mean_temperature = mean_temperature  # °C
        self.surface_pressure = surface_pressure  # bars
        self.has_ring_system = has_ring_system
        self.has_global_magnetic_field = has_global_magnetic_field

        # Moons
        self.moon_objects = []

    def update_position(self, time_scale=1.0):
        """Update planet position based on orbital motion"""
        self.angle += self.orbital_speed * time_scale
        self.rotation_angle += 0.02 * time_scale  # Planet rotation

        # Calculate position in 3D space with inclination
        self.x = self.distance_from_sun * math.cos(self.angle)
        self.y = self.distance_from_sun * math.sin(self.angle) * math.cos(math.radians(self.orbital_inclination))
        self.z = self.distance_from_sun * math.sin(self.angle) * math.sin(math.radians(self.orbital_inclination))

        # Update moon positions
        for moon in self.moon_objects:
            moon.update_position(time_scale)

    def reset_position(self):
        """Reset planet to initial position"""
        self.angle = self.initial_angle
        self.rotation_angle = 0
        # Reset moon positions
        for moon in self.moon_objects:
            moon.reset_position()


class Moon:
    """Class to represent a moon orbiting a planet"""

    def __init__(self, name, planet, radius, distance, orbital_speed, color, facts=None):
        self.name = name
        self.planet = planet
        self.radius = radius
        self.distance = distance
        self.orbital_speed = orbital_speed
        self.color = color
        self.facts = facts or f"Natural satellite of {planet.name}"
        self.angle = random.uniform(0, 2 * math.pi)
        self.initial_angle = self.angle  # Store initial angle for reset
        self.x = 0
        self.y = 0

    def update_position(self, time_scale=1.0):
        """Update moon position relative to its planet"""
        self.angle += self.orbital_speed * time_scale
        self.x = self.planet.x + self.distance * math.cos(self.angle)
        self.y = self.planet.y + self.distance * math.sin(self.angle)

    def reset_position(self):
        """Reset moon to initial position"""
        self.angle = self.initial_angle


class SolarSystemExplorer:
    def mix_colors(self, color1, color2, ratio):
        """Mix two colors with a given ratio (0-1)"""

        # Convert hex to RGB
        def hex_to_rgb(hex_color):
            hex_color = hex_color.lstrip('#')
            return tuple(int(hex_color[i:i + 2], 16) for i in (0, 2, 4))

        # Convert RGB to hex
        def rgb_to_hex(rgb):
            return '#%02x%02x%02x' % rgb

        rgb1 = hex_to_rgb(color1)
        rgb2 = hex_to_rgb(color2)

        # Mix colors
        mixed = tuple(int(rgb1[i] * ratio + rgb2[i] * (1 - ratio)) for i in range(3))
        return rgb_to_hex(mixed)

    def __init__(self, root):
        self.root = root
        self.root.title("3D Solar System Explorer")
        self.root.geometry("1400x900")
        self.root.configure(bg='#121212')

        # Initialize pygame mixer for background music
        try:
            pygame.mixer.init()
            self.music_initialized = True
        except Exception as e:
            print(f"Music initialization failed: {e}")
            self.music_initialized = False

        # Music control variables
        self.music_playing = False
        self.music_volume = 0.5
        self.current_music_file = None

        # Set window icon
        try:
            if os.path.exists('images/icon.png'):
                img = Image.open('images/icon.png')
                icon = ImageTk.PhotoImage(img)
                self.root.tk.call('wm', 'iconphoto', self.root._w, icon)
        except Exception as e:
            print(f"Error loading icon: {e}")

        # Animation control variables
        self.is_running = False
        self.zoom_factor = 1.0
        self.center_x = 700
        self.center_y = 400
        self.time_scale = 1.0  # Speed multiplier
        self.current_date = datetime.now()
        self.initial_date = datetime.now()  # Store initial date for reset
        self.show_orbits = True
        self.show_names = True
        self.show_moons = True
        self.show_3d = True
        self.theme = 'dark'

        # For 3D perspective
        self.view_angle = 30  # Degrees
        self.depth_factor = 0.5  # How much z affects y position

        # Store loaded images to prevent garbage collection
        self.planet_images = {}
        self.sun_image = None
        self.ring_images = {}

        # Load data
        self.planet_data = self.load_planet_data("planets.csv")
        self.satellite_data = self.load_satellite_data("satellites.csv")

        # Initialize planets with realistic data
        self.planets = self.initialize_planets()
        self.initialize_moons()

        # Load images
        self.load_images()

        # Create GUI
        self.setup_gui()

        self.create_menu_bar()

        # Start animation thread
        self.animation_thread = None

        # Initial draw
        self.draw_solar_system()

    def load_planet_data(self, filename):
        """Load planet data from CSV file"""
        try:
            with open(filename, newline='') as csvfile:
                return {row['planet']: row for row in csv.DictReader(csvfile)}
        except Exception as e:
            print(f"Error loading planet data: {e}")
            return {}

    def load_satellite_data(self, filename):
        """Load satellite data from CSV file"""
        try:
            with open(filename, newline='') as csvfile:
                return list(csv.DictReader(csvfile))
        except Exception as e:
            print(f"Error loading satellite data: {e}")
            return []

    def initialize_planets(self):
        """Initialize all planets with their properties"""
        planets_data = {
            'Mercury': {
                'radius': 5, 'distance': 80, 'speed': 0.04, 'color': '#8C7853',
                'image': 'mercury.jpg', 'axial_tilt': 0.034, 'inclination': 7.0,
                'facts': (
                    "Closest to the Sun. Temperature varies from 800°F to -300°F! "
                    "Has a very thin exosphere. Mercury's year is just 88 Earth days."
                )
            },
            'Venus': {
                'radius': 8, 'distance': 110, 'speed': 0.03, 'color': '#FFC649',
                'image': 'venus.jpg', 'axial_tilt': 177.4, 'inclination': 3.4,
                'facts': (
                    "Hottest planet with surface temperatures over 450°C. "
                    "Spins backward and has a thick, toxic atmosphere of CO₂ with clouds of sulfuric acid."
                )
            },
            'Earth': {
                'radius': 9, 'distance': 150, 'speed': 0.02, 'color': '#6B93D6',
                'image': 'earth.jpg', 'axial_tilt': 23.44, 'inclination': 0.0,
                'facts': (
                    "Our home planet! The only known place with life. "
                    "71% of surface is covered by water. Has a protective magnetic field."
                )
            },
            'Mars': {
                'radius': 7, 'distance': 190, 'speed': 0.015, 'color': '#CD5C5C',
                'image': 'mars.jpg', 'axial_tilt': 25.19, 'inclination': 1.9,
                'facts': (
                    "The Red Planet. Has the largest volcano (Olympus Mons) and canyon (Valles Marineris) "
                    "in the solar system. Thin atmosphere mostly of CO₂."
                )
            },
            'Jupiter': {
                'radius': 25, 'distance': 280, 'speed': 0.008, 'color': '#D8CA9D',
                'image': 'jupiter.jpg', 'axial_tilt': 3.13, 'inclination': 1.3,
                'has_rings': True, 'facts': (
                    "Largest planet. A gas giant with no solid surface. "
                    "Has a Great Red Spot storm larger than Earth! Strong magnetic field and many moons."
                )
            },
            'Saturn': {
                'radius': 22, 'distance': 350, 'speed': 0.006, 'color': '#FAD5A5',
                'image': 'saturn.jpg', 'axial_tilt': 26.73, 'inclination': 2.5,
                'has_rings': True, 'facts': (
                    "Famous for its spectacular ring system made of ice and rock particles. "
                    "Less dense than water - it would float! Has over 80 moons."
                )
            },
            'Uranus': {
                'radius': 15, 'distance': 420, 'speed': 0.004, 'color': '#4FD0E7',
                'image': 'uranus.jpg', 'axial_tilt': 97.77, 'inclination': 0.8,
                'has_rings': True, 'facts': (
                    "Tilted on its side (98°). An ice giant with a cold, windy atmosphere of hydrogen and helium. "
                    "Has faint rings and 27 known moons."
                )
            },
            'Neptune': {
                'radius': 14, 'distance': 480, 'speed': 0.003, 'color': '#4B70DD',
                'image': 'neptune.jpg', 'axial_tilt': 28.32, 'inclination': 1.8,
                'has_rings': True, 'facts': (
                    "Windiest planet with speeds up to 1,200 mph! "
                    "An ice giant with the strongest winds in the solar system. "
                    "Has a dark storm spot and 14 known moons."
                )
            },
            'Pluto': {
                'radius': 3, 'distance': 520, 'speed': 0.002, 'color': '#C0C0C0',
                'image': 'pluto.jpg', 'axial_tilt': 122.53, 'inclination': 17.2,
                'facts': (
                    "A dwarf planet in the Kuiper belt. Has a thin atmosphere that freezes and falls to the surface "
                    "when it's farther from the Sun. Has 5 known moons including Charon."
                )
            }
        }

        planets = []
        for name, data in planets_data.items():
            csv_data = self.planet_data.get(name, {})
            planet = Planet(
                name=name,
                radius=data['radius'],
                distance_from_sun=data['distance'],
                orbital_speed=data['speed'],
                color=data['color'],
                moons=self.count_moons(name),
                facts=data['facts'],
                axial_tilt=data['axial_tilt'],
                orbital_inclination=data['inclination'],
                has_rings=data.get('has_rings', False),
                image_path=data['image'],
                mass=csv_data.get('mass'),
                diameter=csv_data.get('diameter'),
                density=csv_data.get('density'),
                gravity=csv_data.get('gravity'),
                escape_velocity=csv_data.get('escape_velocity'),
                rotation_period=csv_data.get('rotation_period'),
                length_of_day=csv_data.get('length_of_day'),
                perihelion=csv_data.get('perihelion'),
                aphelion=csv_data.get('aphelion'),
                orbital_period=csv_data.get('orbital_period'),
                orbital_velocity=csv_data.get('orbital_velocity'),
                orbital_eccentricity=csv_data.get('orbital_eccentricity'),
                obliquity_to_orbit=csv_data.get('obliquity_to_orbit'),
                mean_temperature=csv_data.get('mean_temperature'),
                surface_pressure=csv_data.get('surface_pressure'),
                has_ring_system=csv_data.get('has_ring_system'),
                has_global_magnetic_field=csv_data.get('has_global_magnetic_field')
            )
            planets.append(planet)

        return planets

    def count_moons(self, planet_name):
        """Count moons for a specific planet"""
        return sum(1 for moon in self.satellite_data if moon['planet'] == planet_name)

    def initialize_moons(self):
        """Initialize moon objects for each planet"""
        moon_data = {
            'Earth': [('Moon', 3, 20, 0.05, '#AAAAAA')],
            'Mars': [('Phobos', 1, 15, 0.1, '#BBBBBB'), ('Deimos', 1, 18, 0.08, '#CCCCCC')],
            'Jupiter': [('Io', 2, 30, 0.15, '#FFE4B5'), ('Europa', 2, 35, 0.12, '#FFF8DC'),
                        ('Ganymede', 3, 40, 0.1, '#F5DEB3'), ('Callisto', 2, 45, 0.08, '#D2B48C')],
            'Saturn': [('Titan', 3, 40, 0.07, '#FFA07A'), ('Rhea', 2, 35, 0.09, '#F0E68C'),
                       ('Iapetus', 2, 50, 0.06, '#CD853F')],
            'Uranus': [('Titania', 2, 30, 0.05, '#ADD8E6'), ('Oberon', 2, 35, 0.045, '#87CEFA')],
            'Neptune': [('Triton', 2, 30, 0.04, '#AFEEEE')],
            'Pluto': [('Charon', 1, 15, 0.03, '#D3D3D3')]
        }

        for planet in self.planets:
            if planet.name in moon_data:
                for moon_info in moon_data[planet.name]:
                    name, radius, distance, speed, color = moon_info
                    moon = Moon(name, planet, radius, distance, speed, color)
                    planet.moon_objects.append(moon)

    def load_images(self):
        """Load planet and ring images"""
        # Load Sun image
        sun_paths = ['images/sun.jpg', 'images/sun.png', 'images/Sun.jpg', 'images/Sun.png']
        for path in sun_paths:
            if os.path.exists(path):
                try:
                    img = Image.open(path)
                    img = img.resize((100, 100), Image.Resampling.LANCZOS)
                    self.sun_image = ImageTk.PhotoImage(img)
                    break
                except Exception as e:
                    print(f"Error loading sun image: {e}")

        # Load planet images
        for planet in self.planets:
            # Try multiple image paths and extensions
            base_path = f"images/{planet.name.lower()}"
            extensions = ['.jpg', '.jpeg', '.png', '.JPG', '.JPEG', '.PNG']

            for ext in extensions:
                path = base_path + ext
                if os.path.exists(path):
                    try:
                        img = Image.open(path)
                        # Create texture map for 3D effect
                        texture = self.create_texture_map(img, planet.color)
                        planet.texture_image = texture
                        # Resize for 2D view
                        size = planet.radius * 2
                        img = img.resize((size, size), Image.Resampling.LANCZOS)
                        planet.image = img
                        planet.photo_image = ImageTk.PhotoImage(img)
                        self.planet_images[planet.name] = planet.photo_image
                        break
                    except Exception as e:
                        print(f"Error loading image for {planet.name}: {e}")

        # Load ring images for Saturn and other ringed planets
        ring_paths = ['images/rings.png', 'images/rings.jpg', 'images/Rings.png']
        for path in ring_paths:
            if os.path.exists(path):
                try:
                    img = Image.open(path)
                    img = img.resize((100, 20), Image.Resampling.LANCZOS)
                    self.ring_images['default'] = ImageTk.PhotoImage(img)
                    break
                except Exception as e:
                    print(f"Error loading ring image: {e}")

    def create_texture_map(self, img, base_color):
        """Create a texture map for 3D effect with lighting"""
        try:
            # Convert to RGBA if not already
            if img.mode != 'RGBA':
                img = img.convert('RGBA')

            # Create a lighting effect
            width, height = img.size
            pixels = img.load()

            for y in range(height):
                for x in range(width):
                    r, g, b, a = pixels[x, y]
                    # Apply lighting based on position (simulate sphere)
                    dx = (x - width / 2) / (width / 2)
                    dy = (y - height / 2) / (height / 2)
                    distance = math.sqrt(dx * dx + dy * dy)

                    if distance <= 1.0:  # Inside circle
                        # Lighting intensity (simulate 3D sphere)
                        intensity = 1.0 - distance * 0.7
                        intensity = max(0.3, min(1.0, intensity))
                        # Adjust color
                        r = int(r * intensity)
                        g = int(g * intensity)
                        b = int(b * intensity)
                        # Keep original alpha
                        pixels[x, y] = (r, g, b, a)
                    else:
                        # Transparent outside
                        pixels[x, y] = (0, 0, 0, 0)

            return img
        except Exception as e:
            print(f"Error creating texture map: {e}")
            return None

    def setup_gui(self):
        """Setup the graphical user interface"""
        # Main frame
        main_frame = tk.Frame(self.root, bg='#121212')
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        # Canvas for solar system visualization
        self.canvas = tk.Canvas(
            main_frame,
            width=1100,
            height=700,
            bg='#000033',
            highlightthickness=0
        )
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 10))

        # Control panel
        control_frame = tk.Frame(main_frame, bg='#252525', width=250)
        control_frame.pack(side=tk.RIGHT, fill=tk.Y)
        control_frame.pack_propagate(False)

        # Title
        title_label = tk.Label(
            control_frame,
            text="3D SOLAR SYSTEM\nEXPLORER",
            font=("Arial", 16, "bold"),
            fg='#4FC3F7',
            bg='#252525'
        )
        title_label.pack(pady=(15, 10))

        # Date display
        self.date_label = tk.Label(
            control_frame,
            text=self.current_date.strftime("%Y-%m-%d"),
            font=("Arial", 12),
            fg='white',
            bg='#252525'
        )
        self.date_label.pack(pady=5)

        # Music controls frame
        music_frame = tk.LabelFrame(
            control_frame,
            text="Music Controls",
            fg='white',
            bg='#252525',
            font=("Arial", 10, "bold")
        )
        music_frame.pack(pady=10, fill=tk.X)

        # Music on/off button
        self.music_btn = tk.Button(
            music_frame,
            text="🎵 Music ON",
            command=self.toggle_music,
            bg='#4CAF50',
            fg='white',
            font=("Arial", 9, "bold"),
            width=12
        )
        self.music_btn.pack(pady=5)

        # Volume control
        volume_frame = tk.Frame(music_frame, bg='#252525')
        volume_frame.pack(pady=5, fill=tk.X)

        tk.Label(volume_frame, text="Volume:", fg='white', bg='#252525').pack(anchor='w')
        self.volume_slider = tk.Scale(
            volume_frame,
            from_=0.0,
            to=1.0,
            resolution=0.1,
            orient=tk.HORIZONTAL,
            command=self.set_volume,
            bg='#252525',
            fg='white',
            highlightthickness=0,
            troughcolor='#4FC3F7',
            activebackground='#4FC3F7'
        )
        self.volume_slider.set(0.5)
        self.volume_slider.pack(fill=tk.X)

        # Load music button
        load_music_btn = tk.Button(
            music_frame,
            text="📁 Load Music",
            command=self.load_music,
            bg='#2196F3',
            fg='white',
            font=("Arial", 9),
            width=12
        )
        load_music_btn.pack(pady=2)

        # Time scale control
        time_frame = tk.Frame(control_frame, bg='#252525')
        time_frame.pack(pady=10, fill=tk.X)

        tk.Label(time_frame, text="Time Speed:", fg='white', bg='#252525').pack(anchor='w')
        self.time_scale_slider = tk.Scale(
            time_frame,
            from_=0.1,
            to=5.0,
            resolution=0.1,
            orient=tk.HORIZONTAL,
            command=self.set_time_scale,
            bg='#252525',
            fg='white',
            highlightthickness=0,
            troughcolor='#4FC3F7',
            activebackground='#4FC3F7'
        )
        self.time_scale_slider.set(1.0)
        self.time_scale_slider.pack(fill=tk.X)

        # Animation controls
        control_btn_frame = tk.Frame(control_frame, bg='#252525')
        control_btn_frame.pack(pady=10)

        self.start_btn = tk.Button(
            control_btn_frame,
            text="▶ Start",
            command=self.start_animation,
            bg='#4CAF50',
            fg='white',
            font=("Arial", 10, "bold"),
            width=8
        )
        self.start_btn.grid(row=0, column=0, padx=2)

        self.pause_btn = tk.Button(
            control_btn_frame,
            text="⏸ Pause",
            command=self.pause_animation,
            bg='#FF9800',
            fg='white',
            font=("Arial", 10, "bold"),
            width=8
        )
        self.pause_btn.grid(row=0, column=1, padx=2)

        self.reset_btn = tk.Button(
            control_btn_frame,
            text="⟲ Reset",
            command=self.reset_view,
            bg='#f44336',
            fg='white',
            font=("Arial", 10, "bold"),
            width=8
        )
        self.reset_btn.grid(row=1, column=0, pady=5, padx=2)

        self.date_btn = tk.Button(
            control_btn_frame,
            text="📅 Today",
            command=self.reset_date,
            bg='#9C27B0',
            fg='white',
            font=("Arial", 10, "bold"),
            width=8
        )
        self.date_btn.grid(row=1, column=1, pady=5, padx=2)

        # Zoom controls
        zoom_frame = tk.Frame(control_frame, bg='#252525')
        zoom_frame.pack(pady=10, fill=tk.X)

        tk.Label(zoom_frame, text="Zoom:", fg='white', bg='#252525').pack(anchor='w')
        zoom_btn_frame = tk.Frame(zoom_frame, bg='#252525')
        zoom_btn_frame.pack(fill=tk.X)

        zoom_in_btn = tk.Button(
            zoom_btn_frame,
            text="+ Zoom In",
            command=self.zoom_in,
            bg='#2196F3',
            fg='white',
            width=10
        )
        zoom_in_btn.pack(side=tk.LEFT, padx=2)

        zoom_out_btn = tk.Button(
            zoom_btn_frame,
            text="- Zoom Out",
            command=self.zoom_out,
            bg='#2196F3',
            fg='white',
            width=10
        )
        zoom_out_btn.pack(side=tk.RIGHT, padx=2)

        # View options
        options_frame = tk.LabelFrame(
            control_frame,
            text="View Options",
            fg='white',
            bg='#252525',
            font=("Arial", 10, "bold")
        )
        options_frame.pack(pady=10, fill=tk.X)

        # Theme selector
        theme_frame = tk.Frame(control_frame, bg='#252525')
        theme_frame.pack(pady=10, fill=tk.X)

        tk.Label(theme_frame, text="Theme:", fg='white', bg='#252525').pack(anchor='w')

        self.theme_var = tk.StringVar(value='dark')
        theme_menu = ttk.OptionMenu(
            theme_frame,
            self.theme_var,
            'dark',
            'dark',
            'light',
            'blue',
            command=self.change_theme
        )
        theme_menu.pack(fill=tk.X)

        self.orbit_var = tk.IntVar(value=1)
        orbit_cb = tk.Checkbutton(
            options_frame,
            text="Show Orbits",
            variable=self.orbit_var,
            command=self.toggle_orbits,
            fg='white',
            bg='#252525',
            selectcolor='black',
            activebackground='#252525',
            activeforeground='white'
        )
        orbit_cb.pack(anchor='w')

        self.name_var = tk.IntVar(value=1)
        name_cb = tk.Checkbutton(
            options_frame,
            text="Show Names",
            variable=self.name_var,
            command=self.toggle_names,
            fg='white',
            bg='#252525',
            selectcolor='black',
            activebackground='#252525',
            activeforeground='white'
        )
        name_cb.pack(anchor='w')

        self.moon_var = tk.IntVar(value=1)
        moon_cb = tk.Checkbutton(
            options_frame,
            text="Show Moons",
            variable=self.moon_var,
            command=self.toggle_moons,
            fg='white',
            bg='#252525',
            selectcolor='black',
            activebackground='#252525',
            activeforeground='white'
        )
        moon_cb.pack(anchor='w')

        self.d3_var = tk.IntVar(value=1)
        d3_cb = tk.Checkbutton(
            options_frame,
            text="3D View",
            variable=self.d3_var,
            command=self.toggle_3d,
            fg='white',
            bg='#252525',
            selectcolor='black',
            activebackground='#252525',
            activeforeground='white'
        )
        d3_cb.pack(anchor='w')

        # Planet selection
        planet_frame = tk.LabelFrame(
            control_frame,
            text="Planet Info",
            fg='white',
            bg='#252525',
            font=("Arial", 10, "bold")
        )
        planet_frame.pack(pady=10, fill=tk.X)

        self.planet_combo = ttk.Combobox(
            planet_frame,
            values=[planet.name for planet in self.planets],
            state="readonly",
            width=20
        )
        self.planet_combo.pack(pady=5)
        self.planet_combo.bind('<<ComboboxSelected>>', self.show_planet_info)

        # Info display button
        info_btn = tk.Button(
            planet_frame,
            text="📊 Detailed Info",
            command=self.show_detailed_info,
            bg='#673AB7',
            fg='white',
            font=("Arial", 9),
            width=15
        )
        info_btn.pack(pady=5)

        # Canvas bindings for interaction
        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.canvas.bind("<B1-Motion>", self.on_canvas_drag)
        self.canvas.bind("<MouseWheel>", self.on_mouse_wheel)
        self.canvas.bind("<Motion>", self.on_mouse_move)

        # Variables for dragging
        self.last_x = 0
        self.last_y = 0
        self.dragging = False

    def change_theme(self, theme_name):
        """Change the color theme"""
        self.theme = theme_name
        themes = {
            'dark': {'bg': '#000033', 'text': '#FFFFFF'},
            'light': {'bg': '#E6F3FF', 'text': '#000000'},
            'blue': {'bg': '#001122', 'text': '#00FFFF'}
        }

        if theme_name in themes:
            self.canvas.configure(bg=themes[theme_name]['bg'])
            self.draw_solar_system()

    def create_menu_bar(self):
        """Create menu bar with File, View, and Help menus"""
        menubar = tk.Menu(self.root)
        self.root.config(menu=menubar)

        # File Menu
        file_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="Save Screenshot", command=self.save_screenshot)
        file_menu.add_command(label="Export Data", command=self.export_data)
        file_menu.add_separator()
        file_menu.add_command(label="Load Custom Music", command=self.load_music)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.root.quit)

        # View Menu
        view_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="View", menu=view_menu)
        view_menu.add_checkbutton(label="Show Orbits", variable=self.orbit_var, command=self.toggle_orbits)
        view_menu.add_checkbutton(label="Show Names", variable=self.name_var, command=self.toggle_names)
        view_menu.add_checkbutton(label="Show Moons", variable=self.moon_var, command=self.toggle_moons)
        view_menu.add_checkbutton(label="3D View", variable=self.d3_var, command=self.toggle_3d)
        view_menu.add_separator()
        view_menu.add_command(label="Reset View", command=self.reset_view)
        view_menu.add_command(label="Zoom In", command=self.zoom_in)
        view_menu.add_command(label="Zoom Out", command=self.zoom_out)
        view_menu.add_separator()
        view_menu.add_command(label="Full Screen", command=self.toggle_fullscreen)

        # Help Menu
        help_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Help", menu=help_menu)
        help_menu.add_command(label="Controls", command=self.show_controls)
        help_menu.add_command(label="About Planets", command=self.show_about_planets)
        help_menu.add_separator()
        help_menu.add_command(label="About", command=self.show_about)

    def save_screenshot(self):
        """Save a screenshot of the current view"""
        try:
            filename = filedialog.asksaveasfilename(
                title="Save Screenshot",
                defaultextension=".png",
                filetypes=[("PNG files", "*.png"), ("JPEG files", "*.jpg"), ("All files", "*.*")]
            )
            if filename:
                # Get canvas dimensions
                x = self.canvas.winfo_rootx()
                y = self.canvas.winfo_rooty()
                x1 = x + self.canvas.winfo_width()
                y1 = y + self.canvas.winfo_height()

                # Take screenshot using PIL
                from PIL import ImageGrab
                screenshot = ImageGrab.grab(bbox=(x, y, x1, y1))
                screenshot.save(filename)
                messagebox.showinfo("Screenshot Saved", f"Screenshot saved as {os.path.basename(filename)}")
        except Exception as e:
            messagebox.showerror("Error", f"Could not save screenshot: {e}")

    def export_data(self):
        """Export planet data to CSV"""
        try:
            filename = filedialog.asksaveasfilename(
                title="Export Planet Data",
                defaultextension=".csv",
                filetypes=[("CSV files", "*.csv"), ("All files", "*.*")]
            )
            if filename:
                with open(filename, 'w', newline='') as csvfile:
                    fieldnames = ['Name', 'Distance_from_Sun', 'Radius', 'Orbital_Speed',
                                  'Color', 'Moons', 'Axial_Tilt', 'Orbital_Inclination', 'Has_Rings']
                    writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
                    writer.writeheader()

                    for planet in self.planets:
                        writer.writerow({
                            'Name': planet.name,
                            'Distance_from_Sun': planet.distance_from_sun,
                            'Radius': planet.radius,
                            'Orbital_Speed': planet.orbital_speed,
                            'Color': planet.color,
                            'Moons': planet.moons,
                            'Axial_Tilt': planet.axial_tilt,
                            'Orbital_Inclination': planet.orbital_inclination,
                            'Has_Rings': planet.has_rings
                        })
                messagebox.showinfo("Data Exported", f"Planet data exported to {os.path.basename(filename)}")
        except Exception as e:
            messagebox.showerror("Error", f"Could not export data: {e}")

    def toggle_fullscreen(self):
        """Toggle fullscreen mode"""
        if not hasattr(self, 'is_fullscreen'):
            self.is_fullscreen = False

        self.is_fullscreen = not self.is_fullscreen
        self.root.attributes('-fullscreen', self.is_fullscreen)

        if self.is_fullscreen:
            self.root.bind('<Escape>', lambda e: self.toggle_fullscreen())
        else:
            self.root.unbind('<Escape>')

    def show_controls(self):
        """Show controls help dialog"""
        controls_text = """
    SOLAR SYSTEM EXPLORER - CONTROLS

    🖱️ MOUSE CONTROLS:
    • Left Click + Drag: Pan the view
    • Mouse Wheel: Zoom in/out
    • Click on Planet: Select and show info

    ⌨️ KEYBOARD SHORTCUTS:
    • Escape: Exit fullscreen mode

    🎮 INTERFACE CONTROLS:
    • Start/Pause: Control animation
    • Reset: Reset view and positions
    • Time Speed: Control animation speed
    • Zoom In/Out: Adjust view scale

    🔧 VIEW OPTIONS:
    • Show Orbits: Toggle orbital paths
    • Show Names: Toggle planet labels
    • Show Moons: Toggle moon visibility
    • 3D View: Enable 3D perspective

    🎵 MUSIC CONTROLS:
    • Load Music: Add background music
    • Volume: Adjust music volume
    • Music ON/OFF: Toggle playback

    📊 PLANET INFO:
    • Select planet from dropdown
    • Click "Detailed Info" for full data
    • Click directly on planets for quick info
        """

        info_window = tk.Toplevel(self.root)
        info_window.title("Controls Help")
        info_window.geometry("500x600")
        info_window.configure(bg='#252525')

        text_widget = tk.Text(
            info_window,
            wrap=tk.WORD,
            bg='#121212',
            fg='white',
            font=("Arial", 10),
            padx=15,
            pady=15
        )
        text_widget.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        text_widget.insert(tk.END, controls_text)
        text_widget.config(state=tk.DISABLED)

    def show_about_planets(self):
        """Show information about the solar system"""
        about_text = """
    🌌 ABOUT OUR SOLAR SYSTEM

    Our solar system consists of the Sun and all celestial objects that orbit it, including planets, moons, asteroids, and comets.

    🪐 THE PLANETS:

    INNER PLANETS (Rocky):
    • Mercury: Closest to Sun, extreme temperatures
    • Venus: Hottest planet, thick toxic atmosphere
    • Earth: Our home, the only known planet with life
    • Mars: The Red Planet, largest volcano in solar system

    OUTER PLANETS (Gas/Ice Giants):
    • Jupiter: Largest planet, Great Red Spot storm
    • Saturn: Famous rings, less dense than water
    • Uranus: Tilted on its side, ice giant
    • Neptune: Windiest planet, deep blue color

    🌙 MOONS:
    Our solar system has over 200 known moons, from tiny asteroids to bodies larger than Mercury.

    ⭐ INTERESTING FACTS:
    • The Sun contains 99.86% of the solar system's mass
    • Jupiter has more than 80 known moons
    • Saturn's rings are made of ice and rock particles
    • Venus rotates backwards compared to most planets
    • Mars has seasons like Earth due to its axial tilt

    This simulator shows the relative positions and movements of planets, though distances and sizes are scaled for visibility.
        """

        info_window = tk.Toplevel(self.root)
        info_window.title("About Our Solar System")
        info_window.geometry("600x700")
        info_window.configure(bg='#252525')

        text_widget = tk.Text(
            info_window,
            wrap=tk.WORD,
            bg='#121212',
            fg='white',
            font=("Arial", 11),
            padx=15,
            pady=15
        )
        text_widget.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        text_widget.insert(tk.END, about_text)
        text_widget.config(state=tk.DISABLED)

    def show_about(self):
        """Show about dialog"""
        about_text = """
    🚀 3D SOLAR SYSTEM EXPLORER
    Enhanced Edition

    Version: 2.0
    Created with Python & Tkinter

    FEATURES:
    ✨ Interactive 3D solar system simulation
    🪐 Detailed planet information and facts
    🌙 Moon orbits and visibility
    🎵 Background music support
    📊 Scientific data display
    🖼️ Planet texture mapping
    ⚙️ Customizable view options
    📸 Screenshot capture
    📤 Data export functionality

    TECHNOLOGIES USED:
    • Python 3.x
    • Tkinter (GUI)
    • PIL/Pillow (Image processing)
    • Pygame (Audio)
    • CSV (Data handling)

    EDUCATIONAL PURPOSE:
    This application is designed to help students and astronomy enthusiasts explore and learn about our solar system in an interactive way.

    © 2025 Solar System Explorer
    Made By: Anas Ahmed Qureshi
        """

        messagebox.showinfo("About Solar System Explorer", about_text)

    def toggle_music(self):
        """Toggle background music on/off"""
        if not self.music_initialized:
            messagebox.showwarning("Music Error", "Music system not initialized!")
            return

        if self.music_playing:
            pygame.mixer.music.stop()
            self.music_playing = False
            self.music_btn.config(text="🎵 Music OFF", bg='#f44336')
        else:
            if self.current_music_file and os.path.exists(self.current_music_file):
                try:
                    pygame.mixer.music.load(self.current_music_file)
                    pygame.mixer.music.play(-1)  # Loop indefinitely
                    pygame.mixer.music.set_volume(self.music_volume)
                    self.music_playing = True
                    self.music_btn.config(text="🎵 Music ON", bg='#4CAF50')
                except Exception as e:
                    messagebox.showerror("Music Error", f"Could not play music: {e}")
            else:
                messagebox.showinfo("No Music", "Please load a music file first!")

    def load_music(self):
        """Load a music file"""
        if not self.music_initialized:
            messagebox.showwarning("Music Error", "Music system not initialized!")
            return

        filetypes = [
            ("Audio files", "*.mp3 *.wav *.ogg"),
            ("MP3 files", "*.mp3"),
            ("WAV files", "*.wav"),
            ("OGG files", "*.ogg"),
            ("All files", "*.*")
        ]

        filename = filedialog.askopenfilename(
            title="Select Music File",
            filetypes=filetypes
        )

        if filename:
            self.current_music_file = filename
            messagebox.showinfo("Music Loaded", f"Loaded: {os.path.basename(filename)}")

    def set_volume(self, value):
        """Set music volume"""
        if self.music_initialized:
            self.music_volume = float(value)
            if self.music_playing:
                pygame.mixer.music.set_volume(self.music_volume)

    def set_time_scale(self, value):
        """Set animation time scale"""
        self.time_scale = float(value)

    def start_animation(self):
        """Start the animation"""
        if not self.is_running:
            self.is_running = True
            if self.animation_thread is None or not self.animation_thread.is_alive():
                self.animation_thread = threading.Thread(target=self.animate)
                self.animation_thread.daemon = True
                self.animation_thread.start()

    def pause_animation(self):
        """Pause the animation"""
        self.is_running = False

    def reset_view(self):
        """Reset the view to initial state"""
        self.zoom_factor = 1.0
        self.center_x = 700
        self.center_y = 400
        for planet in self.planets:
            planet.reset_position()
        self.draw_solar_system()

    def reset_date(self):
        """Reset date to current date"""
        self.current_date = datetime.now()
        self.initial_date = datetime.now()
        self.date_label.config(text=self.current_date.strftime("%Y-%m-%d"))

    def zoom_in(self):
        """Zoom in the view"""
        self.zoom_factor *= 1.2
        self.draw_solar_system()

    def zoom_out(self):
        """Zoom out the view"""
        self.zoom_factor /= 1.2
        self.draw_solar_system()

    def toggle_orbits(self):
        """Toggle orbit visibility"""
        self.show_orbits = bool(self.orbit_var.get())
        self.draw_solar_system()

    def toggle_names(self):
        """Toggle name visibility"""
        self.show_names = bool(self.name_var.get())
        self.draw_solar_system()

    def toggle_moons(self):
        """Toggle moon visibility"""
        self.show_moons = bool(self.moon_var.get())
        self.draw_solar_system()

    def toggle_3d(self):
        """Toggle 3D view"""
        self.show_3d = bool(self.d3_var.get())
        self.draw_solar_system()

    def show_planet_info(self, event=None):
        """Show information about selected planet"""
        selected = self.planet_combo.get()
        if selected:
            planet = next((p for p in self.planets if p.name == selected), None)
            if planet:
                info_text = f"{planet.name}\n\nFacts: {planet.facts}\n\nMoons: {planet.moons}"
                messagebox.showinfo(f"{planet.name} Information", info_text)

    def show_detailed_info(self):
        """Show detailed scientific information about selected planet"""
        selected = self.planet_combo.get()
        if not selected:
            messagebox.showwarning("No Selection", "Please select a planet first!")
            return

        planet = next((p for p in self.planets if p.name == selected), None)
        if not planet:
            return

        # Create detailed info window
        info_window = tk.Toplevel(self.root)
        info_window.title(f"{planet.name} - Detailed Information")
        info_window.geometry("500x600")
        info_window.configure(bg='#252525')

        # Create scrollable text widget
        frame = tk.Frame(info_window, bg='#252525')
        frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        text_widget = tk.Text(
            frame,
            wrap=tk.WORD,
            bg='#121212',
            fg='white',
            font=("Arial", 11),
            padx=10,
            pady=10
        )
        scrollbar = tk.Scrollbar(frame, command=text_widget.yview)
        text_widget.config(yscrollcommand=scrollbar.set)

        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        text_widget.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # Format detailed information
        info_text = f"🪐 {planet.name.upper()} - DETAILED INFORMATION\n\n"

        # Basic facts
        info_text += f"📋 BASIC FACTS:\n{planet.facts}\n\n"

        # Physical properties
        info_text += "🔬 PHYSICAL PROPERTIES:\n"
        if planet.mass:
            info_text += f"• Mass: {planet.mass} × 10²⁴ kg\n"
        if planet.diameter:
            info_text += f"• Diameter: {planet.diameter} km\n"
        if planet.density:
            info_text += f"• Density: {planet.density} kg/m³\n"
        if planet.gravity:
            info_text += f"• Surface Gravity: {planet.gravity} m/s²\n"
        if planet.escape_velocity:
            info_text += f"• Escape Velocity: {planet.escape_velocity} km/s\n"

        # Rotational properties
        info_text += "\n🔄 ROTATION:\n"
        if planet.rotation_period:
            info_text += f"• Rotation Period: {planet.rotation_period} hours\n"
        if planet.length_of_day:
            info_text += f"• Length of Day: {planet.length_of_day} hours\n"
        info_text += f"• Axial Tilt: {planet.axial_tilt}°\n"

        # Orbital properties
        info_text += "\n🌌 ORBITAL PROPERTIES:\n"
        if planet.orbital_period:
            info_text += f"• Orbital Period: {planet.orbital_period} days\n"
        if planet.orbital_velocity:
            info_text += f"• Orbital Velocity: {planet.orbital_velocity} km/s\n"
        if planet.perihelion:
            info_text += f"• Perihelion: {planet.perihelion} × 10⁶ km\n"
        if planet.aphelion:
            info_text += f"• Aphelion: {planet.aphelion} × 10⁶ km\n"
        if planet.orbital_eccentricity:
            info_text += f"• Orbital Eccentricity: {planet.orbital_eccentricity}\n"
        info_text += f"• Orbital Inclination: {planet.orbital_inclination}°\n"

        # Atmospheric properties
        info_text += "\n🌡️ ATMOSPHERIC CONDITIONS:\n"
        if planet.mean_temperature:
            info_text += f"• Mean Temperature: {planet.mean_temperature}°C\n"
        if planet.surface_pressure:
            info_text += f"• Surface Pressure: {planet.surface_pressure} bars\n"

        # Other features
        info_text += "\n✨ SPECIAL FEATURES:\n"
        if planet.has_ring_system:
            info_text += f"• Ring System: {planet.has_ring_system}\n"
        if planet.has_global_magnetic_field:
            info_text += f"• Magnetic Field: {planet.has_global_magnetic_field}\n"
        info_text += f"• Number of Moons: {planet.moons}\n"

        if planet.moon_objects:
            info_text += f"\n🌙 MAJOR MOONS:\n"
            for moon in planet.moon_objects:
                info_text += f"• {moon.name}\n"

        text_widget.insert(tk.END, info_text)
        text_widget.config(state=tk.DISABLED)

    def on_canvas_click(self, event):
        """Handle canvas click events"""
        self.last_x = event.x
        self.last_y = event.y
        self.dragging = True

        # Check if clicked on a planet
        clicked_planet = self.get_planet_at_position(event.x, event.y)
        if clicked_planet:
            self.planet_combo.set(clicked_planet.name)
            self.show_planet_info()

    def on_canvas_drag(self, event):
        """Handle canvas drag events"""
        if self.dragging:
            dx = event.x - self.last_x
            dy = event.y - self.last_y
            self.center_x += dx
            self.center_y += dy
            self.last_x = event.x
            self.last_y = event.y
            self.draw_solar_system()

    def on_mouse_wheel(self, event):
        """Handle mouse wheel for zooming"""
        if event.delta > 0:
            self.zoom_factor *= 1.1
        else:
            self.zoom_factor /= 1.1
        self.draw_solar_system()

    def on_mouse_move(self, event):
        """Handle mouse movement for hover effects"""
        planet = self.get_planet_at_position(event.x, event.y)
        if planet:
            self.canvas.config(cursor="hand2")
        else:
            self.canvas.config(cursor="")

    def get_planet_at_position(self, x, y):
        """Get planet at given canvas position"""
        for planet in self.planets:
            px = self.center_x + planet.x * self.zoom_factor
            py = self.center_y + planet.y * self.zoom_factor
            if self.show_3d:
                py += planet.z * self.depth_factor * self.zoom_factor
            distance = math.sqrt((x - px) ** 2 + (y - py) ** 2)
            if distance <= planet.radius * self.zoom_factor:
                return planet
        return None

    def animate(self):
        """Main animation loop"""
        while self.is_running:
            # Update planet positions
            for planet in self.planets:
                planet.update_position(self.time_scale)

            # Update date
            self.current_date += timedelta(days=self.time_scale)

            # Update GUI in main thread
            self.root.after(0, self.update_gui)
            time.sleep(0.05)  # ~20 FPS

    def update_gui(self):
        """Update GUI elements (called from main thread)"""
        self.date_label.config(text=self.current_date.strftime("%Y-%m-%d"))
        self.draw_solar_system()

    def draw_solar_system(self):
        """Draw the entire solar system"""
        self.canvas.delete("all")

        # Draw starfield background
        self.draw_starfield()

        # Draw orbits
        if self.show_orbits:
            self.draw_orbits()

        # Draw Sun
        self.draw_sun()

        # Draw planets (sorted by z-coordinate for proper 3D layering)
        planets_sorted = sorted(self.planets, key=lambda p: p.z if self.show_3d else 0)
        for planet in planets_sorted:
            self.draw_planet(planet)

            # Draw moons
            if self.show_moons:
                for moon in planet.moon_objects:
                    self.draw_moon(moon)

    def draw_starfield(self):
        """Draw background stars"""
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()

        # Use deterministic random seed for consistent star positions
        random.seed(42)
        for _ in range(100):
            x = random.randint(0, canvas_width)
            y = random.randint(0, canvas_height)
            brightness = random.uniform(0.3, 1.0)
            color = self.mix_colors('#FFFFFF', '#000033', brightness)
            size = random.choice([1, 1, 1, 2])  # Mostly small stars
            self.canvas.create_oval(x, y, x + size, y + size, fill=color, outline=color)

    def draw_orbits(self):
        """Draw planetary orbits"""
        for planet in self.planets:
            orbit_radius = planet.distance_from_sun * self.zoom_factor
            if self.show_3d:
                # Draw elliptical orbit for 3D view
                inclination_factor = math.cos(math.radians(planet.orbital_inclination))
                self.canvas.create_oval(
                    self.center_x - orbit_radius,
                    self.center_y - orbit_radius * inclination_factor,
                    self.center_x + orbit_radius,
                    self.center_y + orbit_radius * inclination_factor,
                    outline='#444444',
                    width=1
                )
            else:
                # Draw circular orbit for 2D view
                self.canvas.create_oval(
                    self.center_x - orbit_radius,
                    self.center_y - orbit_radius,
                    self.center_x + orbit_radius,
                    self.center_y + orbit_radius,
                    outline='#444444',
                    width=1
                )

    def draw_sun(self):
        """Draw the Sun at the center"""
        sun_radius = 20 * self.zoom_factor
        if self.sun_image:
            # Draw sun image
            try:
                self.canvas.create_image(
                    self.center_x,
                    self.center_y,
                    image=self.sun_image
                )
            except:
                # Fallback to circle
                self.canvas.create_oval(
                    self.center_x - sun_radius,
                    self.center_y - sun_radius,
                    self.center_x + sun_radius,
                    self.center_y + sun_radius,
                    fill='#FFD700',
                    outline='#FFA500',
                    width=2
                )
        else:
            # Draw sun as gradient circle
            for i in range(int(sun_radius), 0, -2):
                intensity = 1.0 - (sun_radius - i) / sun_radius
                color = self.mix_colors('#FFD700', '#FFA500', intensity)
                self.canvas.create_oval(
                    self.center_x - i,
                    self.center_y - i,
                    self.center_x + i,
                    self.center_y + i,
                    fill=color,
                    outline=color
                )

        # Sun label
        if self.show_names:
            self.canvas.create_text(
                self.center_x,
                self.center_y + sun_radius + 15,
                text="Sun",
                fill='#FFD700',
                font=("Arial", 10, "bold")
            )

    def draw_planet(self, planet):
        """Draw a planet"""
        # Calculate screen position
        x = self.center_x + planet.x * self.zoom_factor
        y = self.center_y + planet.y * self.zoom_factor
        if self.show_3d:
            y += planet.z * self.depth_factor * self.zoom_factor
        radius = planet.radius * self.zoom_factor

        # Draw planet shadow for 3D effect
        if self.show_3d and planet.z > 0:
            shadow_offset = 3
            self.canvas.create_oval(
                x - radius + shadow_offset,
                y - radius + shadow_offset,
                x + radius + shadow_offset,
                y + radius + shadow_offset,
                fill='#000000',
                outline='',
                stipple='gray50'
            )

        # Draw planet
        if planet.photo_image and radius > 5:
            # Scale image to current zoom level
            try:
                if planet.image:
                    scaled_size = max(int(radius * 2), 10)
                    scaled_img = planet.image.resize((scaled_size, scaled_size),
                                                     Image.Resampling.LANCZOS)
                    scaled_photo = ImageTk.PhotoImage(scaled_img)
                    # Store reference to prevent garbage collection
                    planet.current_photo = scaled_photo
                    self.canvas.create_image(x, y, image=scaled_photo)
                else:
                    self.canvas.create_image(x, y, image=planet.photo_image)
            except:
                # Fallback to colored circle
                self.draw_planet_circle(planet, x, y, radius)
        else:
            # Draw as colored circle
            self.draw_planet_circle(planet, x, y, radius)

        # Draw rings if planet has them
        if planet.has_rings and radius > 8:
            self.draw_rings(planet, x, y, radius)

        # Draw planet name
        if self.show_names:
            name_y = y + radius + 12
            self.canvas.create_text(
                x, name_y,
                text=planet.name,
                fill='white',
                font=("Arial", 8, "bold")
            )

    def draw_planet_circle(self, planet, x, y, radius):
        """Draw planet as a colored circle with 3D shading"""
        if self.show_3d:
            # Draw 3D shaded circle
            for i in range(int(radius), 0, -1):
                # Calculate shading based on distance from center
                intensity = 0.4 + 0.6 * (radius - i) / radius
                shaded_color = self.mix_colors(planet.color, '#000000', intensity)
                self.canvas.create_oval(
                    x - i, y - i,
                    x + i, y + i,
                    fill=shaded_color,
                    outline=shaded_color
                )
        else:
            # Draw simple colored circle
            self.canvas.create_oval(
                x - radius, y - radius,
                x + radius, y + radius,
                fill=planet.color,
                outline='white',
                width=1
            )

    def draw_rings(self, planet, x, y, radius):
        """Draw planet rings"""
        ring_outer = radius * 1.8
        ring_inner = radius * 1.3
        ring_thickness = 3

        # Draw multiple ring bands
        for i, alpha in enumerate([0.8, 0.6, 0.4]):
            ring_radius = ring_inner + (ring_outer - ring_inner) * (i + 1) / 3
            ring_color = self.mix_colors('#CCCCCC', planet.color, alpha)

            # Draw ring as flattened ellipse for 3D effect
            if self.show_3d:
                ring_height = ring_radius * 0.2  # Flattened for perspective
                self.canvas.create_oval(
                    x - ring_radius, y - ring_height,
                    x + ring_radius, y + ring_height,
                    outline=ring_color,
                    width=ring_thickness
                )
            else:
                self.canvas.create_oval(
                    x - ring_radius, y - ring_radius,
                    x + ring_radius, y + ring_radius,
                    outline=ring_color,
                    width=ring_thickness
                )

    def draw_moon(self, moon):
        """Draw a moon"""
        moon_radius = moon.radius * self.zoom_factor
        if moon_radius < 1:
            moon_radius = 1

        x = self.center_x + moon.x * self.zoom_factor
        y = self.center_y + moon.y * self.zoom_factor

        # Draw moon
        self.canvas.create_oval(
            x - moon_radius,
            y - moon_radius,
            x + moon_radius,
            y + moon_radius,
            fill=moon.color,
            outline='white',
            width=1
        )

        # Draw moon name for larger moons
        if self.show_names and moon_radius > 2:
            self.canvas.create_text(
                x, y + moon_radius + 8,
                text=moon.name,
                fill='#CCCCCC',
                font=("Arial", 7)
            )

    def run(self):
        """Start the application"""
        self.root.mainloop()

if __name__ == "__main__":
    root = tk.Tk()
    app = SolarSystemExplorer(root)
    app.run()

