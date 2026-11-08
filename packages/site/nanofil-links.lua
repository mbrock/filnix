-- Rewrites links in nanofil/docs/*.md for the rendered site, where they
-- become nanofil/docs/*.html: foo.md becomes foo.html, ../src/F.pl the
-- dterm page ../F.html, concepts/ID.md the concept page
-- ../concept-ID.html (dterm.pl --concepts), and any other path outside nanofil/docs points
-- at GitHub.
local repo = "https://github.com/mbrock/filnix/blob/main/"

function Link(el)
  local target = el.target
  if target:match("^%a[%w+.-]*:") or target:match("^#") then
    return el
  end
  local path, fragment = target:match("^([^#]*)(#?.*)$")
  local module = path:match("^%.%./src/([%w_]+)%.pl$")
  local concept = path:match("^concepts/([%w_.-]+)%.md$")
  if module then
    el.target = "../" .. module .. ".html"
  elseif concept then
    el.target = "../concept-" .. concept .. ".html" .. fragment
  elseif path == "concepts/" or path == "concepts" then
    el.target = "../concepts.html" .. fragment
  elseif path:match("^%.%./%.%./") then
    el.target = repo .. path:sub(7) .. fragment
  elseif path:match("^%.%./") then
    el.target = repo .. "nanofil/" .. path:sub(4) .. fragment
  elseif path:match("^[%w_.-]+%.md$") then
    el.target = path:gsub("%.md$", ".html") .. fragment
  else
    el.target = repo .. "nanofil/docs/" .. path .. fragment
  end
  return el
end
