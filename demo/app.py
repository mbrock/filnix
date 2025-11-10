import msgspec
import cairo
import math
import io
import random
import sqlite3
from contextlib import contextmanager
from datetime import datetime
from pathlib import Path
from starlette.applications import Starlette
from starlette.responses import Response, RedirectResponse, HTMLResponse
from starlette.routing import Route
from tagflow import tag, text, document, html, attr


class Task(msgspec.Struct):
    id: int
    title: str
    completed: bool = False
    created_at: str = msgspec.field(default_factory=lambda: datetime.now().isoformat())


# Initialize SQLite in-memory database
db = sqlite3.connect(":memory:", check_same_thread=False)
db.row_factory = sqlite3.Row

# Create tasks table
db.execute("""
    CREATE TABLE tasks (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        title TEXT NOT NULL,
        completed BOOLEAN NOT NULL DEFAULT 0,
        created_at TEXT NOT NULL
    )
""")

# Insert initial tasks
initial_tasks = [
    ("Build Fil-C with Nix", True, datetime.now().isoformat()),
    ("Port Python to Fil-C", True, datetime.now().isoformat()),
    ("Create demo app", False, datetime.now().isoformat()),
]
db.executemany(
    "INSERT INTO tasks (title, completed, created_at) VALUES (?, ?, ?)",
    initial_tasks,
)
db.commit()


def row_to_task(row: sqlite3.Row) -> Task:
    """Convert SQLite row to Task struct"""
    return Task(
        id=row["id"],
        title=row["title"],
        completed=bool(row["completed"]),
        created_at=row["created_at"],
    )


def get_all_tasks() -> list[Task]:
    """Fetch all tasks from database"""
    cursor = db.execute("SELECT * FROM tasks ORDER BY id")
    return [row_to_task(row) for row in cursor.fetchall()]


def get_task(task_id: int) -> Task | None:
    """Fetch a single task by ID"""
    cursor = db.execute("SELECT * FROM tasks WHERE id = ?", (task_id,))
    row = cursor.fetchone()
    return row_to_task(row) if row else None


def create_task(title: str, completed: bool = False) -> Task:
    """Create a new task in database"""
    created_at = datetime.now().isoformat()
    cursor = db.execute(
        "INSERT INTO tasks (title, completed, created_at) VALUES (?, ?, ?)",
        (title, completed, created_at),
    )
    db.commit()
    return Task(id=cursor.lastrowid, title=title, completed=completed, created_at=created_at)


def update_task(task_id: int, title: str | None = None, completed: bool | None = None) -> Task | None:
    """Update a task in database"""
    task = get_task(task_id)
    if not task:
        return None

    if title is not None:
        db.execute("UPDATE tasks SET title = ? WHERE id = ?", (title, task_id))
    if completed is not None:
        db.execute("UPDATE tasks SET completed = ? WHERE id = ?", (completed, task_id))

    db.commit()
    return get_task(task_id)


def delete_task(task_id: int) -> bool:
    """Delete a task from database"""
    cursor = db.execute("DELETE FROM tasks WHERE id = ?", (task_id,))
    db.commit()
    return cursor.rowcount > 0


@contextmanager
def page(title_text: str):
    """Base page template with Tailwind CSS and HTMX"""
    with tag.html(lang="en"):
        with tag.head():
            with tag.title():
                text(title_text)
            with tag.meta(charset="utf-8"):
                pass
            with tag.meta(name="viewport", content="width=device-width, initial-scale=1"):
                pass
            with tag.script(src="https://cdn.tailwindcss.com"):
                pass
            with tag.script(src="https://unpkg.com/htmx.org@2.0.4"):
                pass
        with tag.body("bg-gray-50 min-h-screen"):
            yield


@html.div(
    "flex items-center gap-4 p-4 bg-white rounded-lg shadow-sm border border-gray-200 transition-all",
)
def task_row(task: Task):
    """Render a single task row with artwork and HTMX interactions"""
    # Set the ID dynamically
    attr("id", f"task-{task.id}")

    text_class = "line-through text-gray-500" if task.completed else "text-gray-900"

    # Task artwork thumbnail
    with tag.a(href=f"/tasks/{task.id}/art", target="_blank", classes="flex-shrink-0"):
        with tag.img(
            src=f"/tasks/{task.id}/art",
            alt=f"Art for {task.title}",
            classes="w-20 h-20 rounded-lg object-cover border-2 border-gray-200 hover:border-blue-400 transition-colors",
        ):
            pass

    # Checkbox with HTMX to toggle completion
    with tag.input(
        type="checkbox",
        classes="w-5 h-5 text-blue-600 rounded focus:ring-2 focus:ring-blue-500 cursor-pointer",
        checked=task.completed,
        hx_post=f"/tasks/{task.id}/toggle",
        hx_target=f"#task-{task.id}",
        hx_swap="outerHTML",
    ):
        pass

    with tag.div("flex-1"):
        with tag.h3(f"text-lg font-medium {text_class}"):
            text(task.title)
        with tag.p("text-sm text-gray-500 mt-1"):
            text(f"Created: {task.created_at}")

    with tag.div("flex items-center gap-2"):
        with tag.span("text-sm text-gray-500"):
            text(f"#{task.id}")
        # Delete button
        with tag.button(
            "px-3 py-1 text-sm bg-red-500 text-white rounded hover:bg-red-600 transition-colors",
            hx_delete=f"/tasks/{task.id}",
            hx_target=f"#task-{task.id}",
            hx_swap="outerHTML swap:1s",
            hx_confirm="Delete this task?",
        ):
            text("🗑️ Delete")


@html.div("mb-6 bg-white p-6 rounded-lg shadow-sm border border-gray-200")
def add_task_form():
    """Render the add task form"""
    with tag.h2("text-xl font-semibold text-gray-800 mb-4"):
        text("Add New Task")
    with tag.form(
        hx_post="/tasks",
        hx_target="#task-list",
        hx_swap="afterbegin",
        hx_on__after_request="this.reset()",
    ):
        with tag.div("flex gap-3"):
            # Input field for task title
            with tag.input(
                type="text",
                name="title",
                placeholder="Enter task title...",
                classes="flex-1 px-4 py-2 border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-transparent",
                required=True,
                autocomplete="off",
            ):
                pass
            with tag.button(
                type="submit",
                classes="px-6 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors font-medium",
            ):
                text("➕ Add Task")


@html.div("space-y-3")
def task_list(tasks: list[Task]):
    """Render the list of tasks"""
    attr("id", "task-list")

    if not tasks:
        with tag.p("text-gray-500 text-center py-8", id="empty-message"):
            text("No tasks yet! Add one above.")
    else:
        for task in tasks:
            task_row(task)


@html.div("mb-8")
def page_header():
    """Render the page header"""
    with tag.h1("text-4xl font-bold text-gray-900 mb-2"):
        text("🏷️ Task Manager")
    with tag.p("text-gray-600 mb-2"):
        text("Built with HTMX + Starlette + msgspec + tagflow + Cairo + SQLite on Fil-C")
    with tag.p("text-sm text-gray-500"):
        text("🛡️ 100% Memory Safe • ")
        with tag.a(href="/deps", classes="text-blue-600 hover:text-blue-800 underline"):
            text("View Dependency Graph")


async def index(request):
    """GET / - HTML view of all tasks with HTMX"""
    tasks = get_all_tasks()

    with document() as root:
        with page("Task Manager - Fil-C Demo"):
            with tag.div("container mx-auto px-4 py-8 max-w-4xl"):
                page_header()
                add_task_form()

                with tag.div("mb-4"):
                    with tag.h2("text-2xl font-semibold text-gray-800"):
                        text(f"Tasks ({len(tasks)})")

                task_list(tasks)

        return Response(root.to_html(), media_type="text/html")


async def htmx_create_task(request):
    """POST /tasks - Create a new task (HTMX)"""
    form = await request.form()
    title = form.get("title", "").strip()

    if not title:
        return Response("", status_code=400)

    task = create_task(title)

    with document() as root:
        task_row(task)

    return Response(root.to_html(), media_type="text/html")


async def htmx_toggle_task(request):
    """POST /tasks/{task_id}/toggle - Toggle task completion (HTMX)"""
    task_id = int(request.path_params["task_id"])
    task = get_task(task_id)

    if not task:
        return Response("", status_code=404)

    # Toggle completion
    updated_task = update_task(task_id, completed=not task.completed)

    with document() as root:
        task_row(updated_task)

    return Response(root.to_html(), media_type="text/html")


async def htmx_delete_task(request):
    """DELETE /tasks/{task_id} - Delete a task (HTMX)"""
    task_id = int(request.path_params["task_id"])

    if not delete_task(task_id):
        return Response("", status_code=404)

    # Return empty response - HTMX will remove the element
    return Response("", media_type="text/html")


def generate_task_art(task_id: int) -> bytes:
    """Generate unique artwork for a task based on its ID using Cairo"""
    # Use task ID as random seed for reproducible artwork
    rng = random.Random(task_id)

    # Create an image surface
    width, height = 400, 400
    surface = cairo.ImageSurface(cairo.FORMAT_ARGB32, width, height)
    ctx = cairo.Context(surface)

    # Random background gradient colors
    bg_r1, bg_g1, bg_b1 = rng.random() * 0.3, rng.random() * 0.3, rng.random() * 0.4
    bg_r2, bg_g2, bg_b2 = rng.random() * 0.4, rng.random() * 0.3, rng.random() * 0.5

    gradient = cairo.LinearGradient(0, 0, width, height)
    gradient.add_color_stop_rgb(0, bg_r1, bg_g1, bg_b1)
    gradient.add_color_stop_rgb(1, bg_r2, bg_g2, bg_b2)
    ctx.set_source(gradient)
    ctx.rectangle(0, 0, width, height)
    ctx.fill()

    center_x, center_y = width / 2, height / 2

    # Choose a random pattern style
    pattern_style = rng.randint(0, 3)

    if pattern_style == 0:
        # Spiraling circles
        num_circles = rng.randint(40, 80)
        spiral_speed = rng.uniform(1.5, 3.5)

        for i in range(num_circles):
            angle = i * math.pi / rng.uniform(6, 10)
            x = center_x + math.cos(angle) * (i * spiral_speed)
            y = center_y + math.sin(angle) * (i * spiral_speed)

            hue = i / num_circles
            r = 0.5 + 0.5 * math.sin(hue * math.pi * 2 + rng.random())
            g = 0.5 + 0.5 * math.sin(hue * math.pi * 2 + 2.09 + rng.random())
            b = 0.5 + 0.5 * math.sin(hue * math.pi * 2 + 4.18 + rng.random())

            ctx.set_source_rgba(r, g, b, rng.uniform(0.1, 0.3))
            ctx.arc(x, y, rng.uniform(15, 35), 0, 2 * math.pi)
            ctx.fill()

    elif pattern_style == 1:
        # Concentric circles with random colors
        num_rings = rng.randint(15, 30)
        for i in range(num_rings):
            radius = (i + 1) * (min(width, height) / 2) / num_rings
            r = 0.3 + 0.7 * rng.random()
            g = 0.3 + 0.7 * rng.random()
            b = 0.3 + 0.7 * rng.random()

            ctx.set_source_rgba(r, g, b, 0.2)
            ctx.arc(center_x, center_y, radius, 0, 2 * math.pi)
            ctx.fill()

    elif pattern_style == 2:
        # Random overlapping polygons
        num_shapes = rng.randint(10, 25)
        for i in range(num_shapes):
            num_sides = rng.randint(3, 8)
            size = rng.uniform(30, 80)
            x = rng.uniform(50, width - 50)
            y = rng.uniform(50, height - 50)
            rotation = rng.uniform(0, 2 * math.pi)

            r = 0.3 + 0.7 * rng.random()
            g = 0.3 + 0.7 * rng.random()
            b = 0.3 + 0.7 * rng.random()
            ctx.set_source_rgba(r, g, b, 0.15)

            ctx.move_to(x + size * math.cos(rotation), y + size * math.sin(rotation))
            for j in range(1, num_sides + 1):
                angle = rotation + j * 2 * math.pi / num_sides
                ctx.line_to(x + size * math.cos(angle), y + size * math.sin(angle))
            ctx.fill()

    else:
        # Radiating lines
        num_lines = rng.randint(20, 50)
        for i in range(num_lines):
            angle = i * 2 * math.pi / num_lines + rng.uniform(-0.1, 0.1)
            length = rng.uniform(80, 180)

            r = 0.5 + 0.5 * math.sin(angle)
            g = 0.5 + 0.5 * math.cos(angle)
            b = 0.5 + 0.5 * math.sin(angle + math.pi / 2)

            ctx.set_source_rgba(r, g, b, 0.3)
            ctx.set_line_width(rng.uniform(2, 6))
            ctx.move_to(center_x, center_y)
            ctx.line_to(center_x + math.cos(angle) * length, center_y + math.sin(angle) * length)
            ctx.stroke()

    # Add some accent circles on top
    num_accents = rng.randint(3, 8)
    for i in range(num_accents):
        x = rng.uniform(50, width - 50)
        y = rng.uniform(50, height - 50)
        r = 0.8 + 0.2 * rng.random()
        g = 0.8 + 0.2 * rng.random()
        b = 0.8 + 0.2 * rng.random()

        ctx.set_source_rgba(r, g, b, 0.1)
        ctx.arc(x, y, rng.uniform(20, 50), 0, 2 * math.pi)
        ctx.fill()

    # Write to PNG in memory
    buffer = io.BytesIO()
    surface.write_to_png(buffer)
    buffer.seek(0)

    return buffer.getvalue()


async def get_task_art(request):
    """GET /tasks/{task_id}/art - Get artwork for a specific task"""
    task_id = int(request.path_params["task_id"])

    if not get_task(task_id):
        # Generate a "not found" image
        surface = cairo.ImageSurface(cairo.FORMAT_ARGB32, 400, 400)
        ctx = cairo.Context(surface)
        ctx.set_source_rgb(0.9, 0.9, 0.9)
        ctx.rectangle(0, 0, 400, 400)
        ctx.fill()

        buffer = io.BytesIO()
        surface.write_to_png(buffer)
        buffer.seek(0)
        return Response(buffer.getvalue(), media_type="image/png")

    art_data = generate_task_art(task_id)
    return Response(art_data, media_type="image/png")


async def dependency_graph(request):
    """GET /deps - Visualize the dependency graph"""
    try:
        import networkx as nx
        from pyvis.network import Network

        # Look for the GraphML file in parent directory
        graphml_path = Path(__file__).parent / "python-web-demo-deps.graphml"

        if not graphml_path.exists():
            return HTMLResponse(
                "<html><body><h1>Dependency Graph Not Found</h1>"
                "<p>Run <code>nix-store -q --graphml $(nix build .#python-web-demo --print-out-paths --no-link) > python-web-demo-deps.graphml</code> first.</p>"
                "</body></html>",
                status_code=404,
            )

        # Load the GraphML file
        G = nx.read_graphml(str(graphml_path))

        # Create pyvis network
        net = Network(
            height="100vh",
            width="100%",
            bgcolor="#0a0a0a",
            font_color="white",
            directed=True,
        )

        # Configure physics for force-directed layout
        net.set_options("""
        {
          "physics": {
            "forceAtlas2Based": {
              "gravitationalConstant": -50,
              "centralGravity": 0.02,
              "springLength": 100,
              "springConstant": 0.08
            },
            "maxVelocity": 50,
            "solver": "forceAtlas2Based",
            "timestep": 0.35,
            "stabilization": {"iterations": 150}
          },
          "nodes": {
            "font": {
              "size": 16,
              "face": "monospace"
            }
          }
        }
        """)

        # Add nodes with clean styling
        for node, data in G.nodes(data=True):
            name = data.get('name', node)
            is_memory_safe = 'gnufilc0' in node

            # Extract clean package name with version (strip store paths)
            if 'python3.12-' in node:
                # Extract from node ID to get the package-version part
                # Format: hash-python3.12-package-version-x86_64...
                parts = node.split('-', 1)
                if len(parts) > 1:
                    # Remove hash prefix
                    rest = parts[1]
                    # Remove python3.12- prefix
                    if rest.startswith('python3.12-'):
                        pkg_with_ver = rest.replace('python3.12-', '', 1)
                        # Remove platform suffix
                        pkg_with_ver = pkg_with_ver.replace('-x86_64-unknown-linux-gnufilc0', '')
                        # Try to split package name from version
                        ver_parts = pkg_with_ver.rsplit('-', 1)
                        if len(ver_parts) == 2 and ver_parts[1][0].isdigit():
                            label = f"{ver_parts[0]} {ver_parts[1]}"
                        else:
                            label = pkg_with_ver
                    else:
                        label = rest[:25]
                else:
                    label = node[:25]
            elif 'python3-3.12' in node:
                label = "python3.12"
            elif 'filc-demo' in node:
                label = "filc-demo"
            else:
                # Generic cleanup - remove hash prefix and platform suffix
                parts = node.split('-', 1)
                if len(parts) > 1:
                    clean = parts[1]
                    clean = clean.replace('-x86_64-unknown-linux-gnufilc0', '')
                    if len(clean) > 30:
                        clean = clean[:30]
                    label = clean
                else:
                    label = node[:30]

            # Simple categorization: memory-safe vs build-time
            if is_memory_safe:
                color = '#006633'
                size = 22
                shape = 'box'
                title = f"MEMORY SAFE: {name}"
                if 'filc-demo' in node:
                    color = '#FFD700'  # Gold for app
                    size = 35
                    shape = 'star'
            else:
                color = '#666666'  # Gray for build-time only
                font_color = '#FFFFFF'  # White text on gray
                size = 15
                shape = 'dot'
                title = f"Build-time: {name}"

            net.add_node(
                node,
                label=label,
                title=title,
                color=color,
                size=size,
                shape=shape,
                font={'color': font_color},
            )

        # Count memory-safe packages
        memory_safe_count = sum(1 for node in G.nodes() if 'gnufilc0' in node)
        total_count = len(G.nodes())

        # Add edges with simple coloring
        for source, target in G.edges():
            if 'gnufilc0' in source:
                edge_color = '#00FF8844'  # Green with transparency for memory-safe
            else:
                edge_color = '#33333333'  # Dark gray for build-time
            net.add_edge(source, target, width=0.5, arrows="to", color=edge_color)

        # Generate HTML
        html = net.generate_html()

        # Add custom legend and stats
        legend_html = f"""
        <style>
            body, html {{
                margin: 0;
                padding: 0;
                overflow: hidden;
                width: 100%;
                height: 100vh;
            }}
            #mynetwork {{
                width: 100%;
                height: 100vh;
                margin: 0;
                padding: 0;
            }}
            .legend {{
                position: fixed;
                top: 10px;
                right: 10px;
                background: rgba(20, 20, 20, 0.95);
                border: 2px solid #FFD700;
                border-radius: 12px;
                padding: 15px;
                color: white;
                font-family: monospace;
                font-size: 12px;
                z-index: 1000;
                max-width: 280px;
                box-shadow: 0 8px 32px rgba(0, 0, 0, 0.8);
                max-height: calc(100vh - 20px);
                overflow-y: auto;
            }}
            .legend h3 {{
                margin: 0 0 12px 0;
                color: #FFD700;
                font-size: 16px;
                border-bottom: 2px solid #FFD700;
                padding-bottom: 6px;
            }}
            .legend-item {{
                display: flex;
                align-items: center;
                margin: 6px 0;
                gap: 8px;
            }}
            .legend-color {{
                width: 16px;
                height: 16px;
                border-radius: 3px;
                border: 1px solid #555;
                flex-shrink: 0;
            }}
            .stats {{
                margin-top: 15px;
                padding-top: 15px;
                border-top: 1px solid #444;
            }}
            .stats-item {{
                margin: 5px 0;
                color: #00FF88;
            }}
        </style>

        """

        return HTMLResponse(html)

    except Exception as e:
        return HTMLResponse(
            f"<html><body><h1>Error loading graph</h1><pre>{str(e)}</pre></body></html>",
            status_code=500,
        )


app = Starlette(
    routes=[
        Route("/", index, methods=["GET"]),
        Route("/tasks", htmx_create_task, methods=["POST"]),
        Route("/tasks/{task_id}/toggle", htmx_toggle_task, methods=["POST"]),
        Route("/tasks/{task_id}", htmx_delete_task, methods=["DELETE"]),
        Route("/tasks/{task_id}/art", get_task_art, methods=["GET"]),
        Route("/deps", dependency_graph, methods=["GET"]),
    ],
)

