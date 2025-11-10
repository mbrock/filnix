import msgspec
import cairo
import math
import io
from contextlib import contextmanager
from datetime import datetime
from starlette.applications import Starlette
from starlette.responses import Response
from starlette.routing import Route
from tagflow import tag, text, document


class Task(msgspec.Struct):
    id: int
    title: str
    completed: bool = False
    created_at: str = msgspec.field(default_factory=lambda: datetime.now().isoformat())


# In-memory task storage
tasks: dict[int, Task] = {
    1: Task(id=1, title="Build Fil-C with Nix", completed=True),
    2: Task(id=2, title="Port Python to Fil-C", completed=True),
    3: Task(id=3, title="Create demo app", completed=False),
}
next_id = 4

encoder = msgspec.json.Encoder()


@contextmanager
def page(title_text: str):
    """Base page template with Tailwind CSS"""
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
        with tag.body("bg-gray-50 min-h-screen"):
            yield


def task_row(task: Task):
    """Render a single task row"""
    checkbox_class = "checked" if task.completed else ""
    text_class = "line-through text-gray-500" if task.completed else "text-gray-900"

    with tag.div("flex items-center gap-4 p-4 bg-white rounded-lg shadow-sm border border-gray-200"):
        with tag.input_(
            type="checkbox",
            classes="w-5 h-5 text-blue-600 rounded focus:ring-2 focus:ring-blue-500",
            checked=task.completed,
            disabled=True,
        ):
            pass
        with tag.div("flex-1"):
            with tag.h3(f"text-lg font-medium {text_class}"):
                text(task.title)
            with tag.p("text-sm text-gray-500 mt-1"):
                text(f"Created: {task.created_at}")
        with tag.div("text-sm text-gray-500"):
            text(f"ID: {task.id}")


async def index(request):
    """GET / - HTML view of all tasks"""
    with document() as root:
        with page("Task Manager - Fil-C Demo"):
            with tag.div("container mx-auto px-4 py-8 max-w-4xl"):
                with tag.div("mb-8"):
                    with tag.h1("text-4xl font-bold text-gray-900 mb-2"):
                        text("🏷️ Task Manager")
                    with tag.p("text-gray-600"):
                        text("Built with Starlette + msgspec + tagflow on Fil-C")

                with tag.div("mb-6 flex justify-between items-center"):
                    with tag.h2("text-2xl font-semibold text-gray-800"):
                        text(f"Tasks ({len(tasks)})")
                    with tag.div("flex gap-3"):
                        with tag.a(
                            href="/art",
                            classes="px-4 py-2 bg-purple-600 text-white rounded-lg hover:bg-purple-700 transition-colors",
                        ):
                            text("🎨 View Cairo Art")
                        with tag.a(
                            href="/api/tasks",
                            classes="px-4 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors",
                        ):
                            text("View JSON API")

                with tag.div("space-y-3"):
                    if not tasks:
                        with tag.p("text-gray-500 text-center py-8"):
                            text("No tasks yet!")
                    else:
                        for task in tasks.values():
                            task_row(task)

        return Response(root.to_html(), media_type="text/html")


async def api_list_tasks(request):
    """GET /api/tasks - JSON API"""
    task_list = {
        "tasks": [msgspec.structs.asdict(t) for t in tasks.values()],
        "total": len(tasks),
    }
    return Response(encoder.encode(task_list), media_type="application/json")


async def api_get_task(request):
    """GET /api/tasks/{task_id} - Get a specific task"""
    task_id = int(request.path_params["task_id"])

    if task_id not in tasks:
        error = {"error": f"Task {task_id} not found"}
        return Response(encoder.encode(error), status_code=404, media_type="application/json")

    return Response(encoder.encode(msgspec.structs.asdict(tasks[task_id])), media_type="application/json")


async def api_create_task(request):
    """POST /api/tasks - Create a new task"""
    global next_id

    try:
        body = await request.body()
        data = msgspec.json.decode(body)

        task = Task(
            id=next_id,
            title=data.get("title", "Untitled"),
            completed=data.get("completed", False),
        )
        tasks[next_id] = task
        next_id += 1

        return Response(encoder.encode(msgspec.structs.asdict(task)), status_code=201, media_type="application/json")
    except Exception as e:
        error = {"error": str(e)}
        return Response(encoder.encode(error), status_code=400, media_type="application/json")


async def api_update_task(request):
    """PUT /api/tasks/{task_id} - Update a task"""
    task_id = int(request.path_params["task_id"])

    if task_id not in tasks:
        error = {"error": f"Task {task_id} not found"}
        return Response(encoder.encode(error), status_code=404, media_type="application/json")

    try:
        body = await request.body()
        data = msgspec.json.decode(body)

        task = tasks[task_id]
        if "title" in data:
            task = msgspec.structs.replace(task, title=data["title"])
        if "completed" in data:
            task = msgspec.structs.replace(task, completed=data["completed"])

        tasks[task_id] = task
        return Response(encoder.encode(msgspec.structs.asdict(task)), media_type="application/json")
    except Exception as e:
        error = {"error": str(e)}
        return Response(encoder.encode(error), status_code=400, media_type="application/json")


async def api_delete_task(request):
    """DELETE /api/tasks/{task_id} - Delete a task"""
    task_id = int(request.path_params["task_id"])

    if task_id not in tasks:
        error = {"error": f"Task {task_id} not found"}
        return Response(encoder.encode(error), status_code=404, media_type="application/json")

    del tasks[task_id]
    return Response(b'{"message": "Task deleted"}', media_type="application/json")


async def draw_art(request):
    """GET /art - Generate a cool geometric pattern using Cairo"""
    # Create an image surface
    width, height = 800, 600
    surface = cairo.ImageSurface(cairo.FORMAT_ARGB32, width, height)
    ctx = cairo.Context(surface)

    # Background gradient
    gradient = cairo.LinearGradient(0, 0, width, height)
    gradient.add_color_stop_rgb(0, 0.1, 0.1, 0.2)
    gradient.add_color_stop_rgb(1, 0.2, 0.1, 0.3)
    ctx.set_source(gradient)
    ctx.rectangle(0, 0, width, height)
    ctx.fill()

    # Draw spiraling circles with varying colors
    center_x, center_y = width / 2, height / 2
    num_circles = 60

    for i in range(num_circles):
        angle = i * math.pi / 8
        radius = 150 + i * 3
        x = center_x + math.cos(angle) * (i * 2.5)
        y = center_y + math.sin(angle) * (i * 2.5)

        # Color based on position in spiral
        hue = i / num_circles
        r = 0.5 + 0.5 * math.sin(hue * math.pi * 2)
        g = 0.5 + 0.5 * math.sin(hue * math.pi * 2 + 2.09)
        b = 0.5 + 0.5 * math.sin(hue * math.pi * 2 + 4.18)

        ctx.set_source_rgba(r, g, b, 0.15)
        ctx.arc(x, y, 30 - i * 0.3, 0, 2 * math.pi)
        ctx.fill()

    # Draw overlapping geometric shapes
    for i in range(12):
        angle = i * math.pi / 6
        x = center_x + math.cos(angle) * 120
        y = center_y + math.sin(angle) * 120

        ctx.set_source_rgba(1, 1, 1, 0.1)
        ctx.set_line_width(2)

        # Draw hexagon
        ctx.move_to(x + 40 * math.cos(0), y + 40 * math.sin(0))
        for j in range(1, 7):
            hex_angle = j * math.pi / 3
            ctx.line_to(x + 40 * math.cos(hex_angle), y + 40 * math.sin(hex_angle))
        ctx.stroke()

    # Add some overlapping translucent circles in the center
    for i in range(8):
        angle = i * math.pi / 4
        offset = 80
        x = center_x + math.cos(angle) * offset
        y = center_y + math.sin(angle) * offset

        ctx.set_source_rgba(0.8, 0.9, 1.0, 0.08)
        ctx.arc(x, y, 60, 0, 2 * math.pi)
        ctx.fill()

    # Write to PNG in memory
    buffer = io.BytesIO()
    surface.write_to_png(buffer)
    buffer.seek(0)

    return Response(buffer.getvalue(), media_type="image/png")


app = Starlette(
    routes=[
        Route("/", index, methods=["GET"]),
        Route("/art", draw_art, methods=["GET"]),
        Route("/api/tasks", api_list_tasks, methods=["GET"]),
        Route("/api/tasks", api_create_task, methods=["POST"]),
        Route("/api/tasks/{task_id}", api_get_task, methods=["GET"]),
        Route("/api/tasks/{task_id}", api_update_task, methods=["PUT"]),
        Route("/api/tasks/{task_id}", api_delete_task, methods=["DELETE"]),
    ],
)

