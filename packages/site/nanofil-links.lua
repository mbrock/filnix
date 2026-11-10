-- Rewrites links in nanofil/docs/*.md for the rendered site, where they
-- become nanofil/docs/*.html: foo.md becomes foo.html, ../src/F.pl the
-- dterm page ../F.html, concepts/ID.md the concept page
-- ../concept-ID.html (dterm.pl --concepts), and any other file its drawn
-- code page, or else GitHub (pages.lua). An archived document (pandoc -M
-- archived) is written in nanofil/docs/archive but rendered beside the
-- others, so its links lose one ../ first; archive/NAME.md, from any
-- document, is NAME.html.
local pages = dofile((PANDOC_SCRIPT_FILE:match("^(.*)/") or ".") .. "/pages.lua")
local archived = false

function Link(el)
  local target = el.target
  if target:match("^%a[%w+.-]*:") or target:match("^#") then
    return el
  end
  local path, fragment = target:match("^([^#]*)(#?.*)$")
  if archived and path:match("^%.%./") then
    path = path:sub(4)
  end
  local old = path:match("^archive/([%w_.-]+)%.md$")
  if old then
    el.target = old .. ".html" .. fragment
    return el
  end
  local concept = path:match("^concepts/([%w_.-]+)%.md$")
  if concept then
    el.target = "../concept-" .. concept .. ".html" .. fragment
  elseif path == "concepts/" or path == "concepts" then
    el.target = "../concepts.html" .. fragment
  elseif path:match("^[%w_.-]+%.md$") then
    el.target = path:gsub("%.md$", ".html") .. fragment
  else
    el.target = pages.href(pages.normalize("nanofil/docs", path), fragment, "nanofil/docs")
  end
  return el
end

return {
  { Meta = function(meta) archived = meta.archived ~= nil end },
  { Link = Link },
}
