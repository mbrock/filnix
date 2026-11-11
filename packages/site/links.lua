-- Rewrites links in docs/*.md for the rendered site: foo.md becomes
-- foo.html, README.md the index, and paths outside docs/ their drawn
-- code page, or else GitHub (pages.lua). An archived document (pandoc -M
-- archived) is written in docs/archive but rendered beside the others, so
-- its links lose one ../ first; archive/NAME.md, from any document, is
-- NAME.html.
-- Mermaid code blocks become <pre class="mermaid"> for mermaid.js.
local pages = dofile((PANDOC_SCRIPT_FILE:match("^(.*)/") or ".") .. "/pages.lua")
local archived = false

local function Link(el)
  local target = el.target
  if target:match("^%a[%w+.-]*:") or target:match("^#") then
    return el
  end
  local path, fragment = target:match("^([^#]*)(#?.*)$")
  if archived and path:match("^%.%./") then
    path = path:sub(4)
  end
  local old = path:match("^archive/([%w_.-]+)$")
  if old then
    el.target = old:gsub("%.md$", ".html") .. fragment
    return el
  end
  if path:match("^%.%./") then
    el.target = pages.href(pages.normalize("docs", path), fragment, "docs")
  elseif path == "README.md" then
    el.target = "index.html" .. fragment
  else
    el.target = path:gsub("%.md$", ".html") .. fragment
  end
  return el
end

local function CodeBlock(el)
  if el.classes[1] == "mermaid" then
    return pandoc.RawBlock("html", '<pre class="mermaid">' .. el.text:gsub("&", "&amp;"):gsub("<", "&lt;") .. "</pre>")
  end
end

return {
  { Meta = function(meta) archived = meta.archived ~= nil end },
  { Link = Link, CodeBlock = CodeBlock },
}
