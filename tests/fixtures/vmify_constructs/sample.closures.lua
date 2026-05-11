-- closures + upvalues fixture for Vmify recognizer/extractor.
local function counter()
    local n = 0
    return function()
        n = n + 1
        return n
    end
end

local c = counter()
print(c(), c(), c())

local function adder(a)
    return function(b)
        return a + b
    end
end

local add5 = adder(5)
print(add5(3))
print(add5(10))
