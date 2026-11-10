-- The site's page for a file of the repository, for the links filters
-- (links.lua, nanofil-links.lua). Each code renderer draws a file as the
-- page its path names. A link goes to that page when the site has it,
-- since build.sh draws every code page into $SITE before pandoc runs.
-- Otherwise it goes to the file on GitHub.
local M = {}

local repo = "https://github.com/mbrock/filnix/blob/main/"

local function dashed(p)
  return (p:gsub("/", "-"))
end

-- A Lua pattern over the repository path, and the page's path in the site.
local rules = {
  -- nanofil/web/dterm.pl: nanofil/src/c_types.pl is nanofil/c_types.html.
  { "^nanofil/src/([%w_]+)%.pl$", function(m) return "nanofil/" .. m .. ".html" end },
  -- dterm-rocq: nanofil/rocq/glibc/ZsysWrite.v is nanofil/rocq/rocq-glibc-ZsysWrite.html.
  { "^nanofil/(.+)%.v$", function(p) return "nanofil/rocq/" .. dashed(p) .. ".html" end },
  -- dterm-nix: nanofil/nix/check.nix is nix/nanofil-nix-check.html.
  { "^(.+)%.nix$", function(p) return "nix/" .. dashed(p) .. ".html" end },
}

local function exists(path)
  local f = io.open(path, "r")
  if f then f:close() end
  return f ~= nil
end

local function split(p)
  local parts = {}
  for s in p:gmatch("[^/]+") do parts[#parts + 1] = s end
  return parts
end

-- normalize("nanofil/docs", "../rocq/X.v") is "nanofil/rocq/X.v".
function M.normalize(dir, rel)
  local parts = split(dir)
  for _, s in ipairs(split(rel)) do
    if s == ".." then
      table.remove(parts)
    elseif s ~= "." then
      parts[#parts + 1] = s
    end
  end
  local p = table.concat(parts, "/")
  if rel:match("/$") then p = p .. "/" end
  return p
end

-- The relative href, from the site directory from, of the site path to.
local function relative(from, to)
  local a, b = split(from), split(to)
  local i = 1
  while i <= #a and i < #b and a[i] == b[i] do i = i + 1 end
  return string.rep("../", #a - i + 1) .. table.concat(b, "/", i)
end

-- href(path, fragment, from): the link to the repository's path from a
-- page in the site directory from: its drawn page, or GitHub.
function M.href(path, fragment, from)
  local site = os.getenv("SITE")
  for _, r in ipairs(rules) do
    local m = path:match(r[1])
    if m then
      local page = r[2](m)
      if site and exists(site .. "/" .. page) then
        return relative(from, page) .. fragment
      end
      break
    end
  end
  return repo .. path .. fragment
end

return M
