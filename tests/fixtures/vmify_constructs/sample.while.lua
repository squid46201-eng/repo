-- while-loop fixture for Vmify recognizer/extractor.
local function countdown(n)
    while n > 0 do
        print(n)
        n = n - 1
    end
    print("done")
end

countdown(3)
