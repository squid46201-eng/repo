-- numeric for-loop fixture for Vmify recognizer/extractor.
local function sum_to(n)
    local total = 0
    for i = 1, n do
        total = total + i
    end
    return total
end

print(sum_to(10))
print(sum_to(0))
