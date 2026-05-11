-- if/elseif/else fixture for Vmify recognizer/extractor.
local function classify(n)
    if n < 0 then
        return "neg"
    elseif n == 0 then
        return "zero"
    elseif n < 10 then
        return "small"
    else
        return "big"
    end
end

print(classify(-5))
print(classify(0))
print(classify(7))
print(classify(99))
