"""Keep build evidence without Nix's high-volume download-progress telemetry."""

import json


class BuildLogFilter:
    def __init__(self):
        self.pending = b""
        self.passthrough = False
        self.omitted_records = 0
        self.omitted_bytes = 0

    def keep(self, line):
        if line.startswith(b"@nix "):
            try:
                event = json.loads(line[5:])
                if (
                    isinstance(event, dict)
                    and event.get("action") == "result"
                    and event.get("type") == 105
                    and isinstance(event.get("fields"), list)
                    and len(event["fields"]) == 4
                    and all(type(value) is int for value in event["fields"])
                ):
                    self.omitted_records += 1
                    self.omitted_bytes += len(line)
                    return b""
            except (ValueError, UnicodeDecodeError):
                pass
        return line

    def feed(self, data):
        self.pending += data
        lines = self.pending.split(b"\n")
        self.pending = lines.pop()
        output = []
        for line in lines:
            line += b"\n"
            output.append(line if self.passthrough else self.keep(line))
            self.passthrough = False
        # Forward an oversized record in pieces. Never buffer it indefinitely,
        # nor interpret a fragment in its middle as a new telemetry record.
        if len(self.pending) > 1024**2:
            output.append(self.pending)
            self.pending = b""
            self.passthrough = True
        return b"".join(output)

    def finish(self):
        # Incomplete records remain raw evidence, even if they resemble progress.
        data, self.pending = self.pending, b""
        return data
