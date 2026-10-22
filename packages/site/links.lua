-- Rewrites links in docs/*.md for the rendered site: foo.md becomes
-- foo.html, README.md the index, and paths outside docs/ point at GitHub.
-- Mermaid code blocks become <pre class="mermaid"> for mermaid.js.
local repo = "https://github.com/mbrock/filnix/blob/main/"

function Link(el)
  local target = el.target
  if target:match("^%a[%w+.-]*:") or target:match("^#") then
    return el
  end
  local path, fragment = target:match("^([^#]*)(#?.*)$")
  if path:match("^%.%./") then
    el.target = repo .. path:sub(4) .. fragment
  elseif path == "README.md" then
    el.target = "index.html" .. fragment
  else
    el.target = path:gsub("%.md$", ".html") .. fragment
  end
  return el
end

function CodeBlock(el)
  if el.classes[1] == "mermaid" then
    return pandoc.RawBlock("html", '<pre class="mermaid">' .. el.text:gsub("&", "&amp;"):gsub("<", "&lt;") .. "</pre>")
  end
end
