-- vararg fixture for Vmify recognizer/extractor.
local function sum(...)
    local n = select("#", ...)
    local total = 0
    for i = 1, n do
        total = total + select(i, ...)
    end
    return total
end

print(sum())
print(sum(1, 2, 3))
print(sum(10, 20, 30, 40, 50))
