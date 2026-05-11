-- generic for-in loop fixture (ipairs / pairs) for Vmify recognizer/extractor.
local t = { "a", "b", "c" }
for i, v in ipairs(t) do
    print(i, v)
end

local m = { x = 1, y = 2 }
for k, v in pairs(m) do
    print(k, v)
end
