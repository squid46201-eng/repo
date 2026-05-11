local function greet(name)
    print("Hello, " .. name .. "!")
    return "greeted_" .. name
end

local r = greet("World")
print("got back:", r)
print("number:", 42)
print("bool:", true)
