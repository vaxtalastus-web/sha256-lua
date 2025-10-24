local MAX_BITS = 32
local MOD = 2 ^ 32
local POW2 = {}
for i = 0, MAX_BITS - 1 do POW2[i] = 2 ^ i end
local function toBits(n)
    local bits = {}
    for i = 0, MAX_BITS - 1 do
        bits[i] = n % 2
        n = math.floor(n / 2)
    end
    return bits
end
local function fromBits(bits)
    local n = 0
    for i = 0, MAX_BITS - 1 do
        n = n + (bits[i] or 0) * POW2[i]
    end
    return n
end
local function norm(n) return n % MOD end
function band(...)
    local args = {...}
    local bits = toBits(norm(args[1]))
    for i = 2, #args do
        local b = toBits(norm(args[i]))
        for j = 0, MAX_BITS - 1 do bits[j] = bits[j] * b[j] end
    end
    return fromBits(bits)
end
function bor(...)
    local args = {...}
    local bits = toBits(norm(args[1]))
    for i = 2, #args do
        local b = toBits(norm(args[i]))
        for j = 0, MAX_BITS - 1 do bits[j] = math.min(1, bits[j] + b[j]) end
    end
    return fromBits(bits)
end
function bxor(...)
    local args = {...}
    local bits = toBits(norm(args[1]))
    for i = 2, #args do
        local b = toBits(norm(args[i]))
        for j = 0, MAX_BITS - 1 do bits[j] = (bits[j] + b[j]) % 2 end
    end
    return fromBits(bits)
end
function bnot(n)
    local bits = toBits(norm(n))
    for i = 0, MAX_BITS - 1 do bits[i] = 1 - bits[i] end
    return fromBits(bits)
end
function lshift(n, bits)
    return norm(n * POW2[bits])
end
function rshift(n, bits)
    return math.floor(norm(n) / POW2[bits])
end
function arshift(n, bits)
    n = norm(n)
    local sign = n >= 2147483648 and 1 or 0
    local shifted = math.floor(n / POW2[bits])
    if sign == 1 then
        local mask = 0
        for i = MAX_BITS - bits, MAX_BITS - 1 do mask = mask + POW2[i] end
        shifted = shifted + mask
    end
    return norm(shifted)
end
local function rrotate(x, n)
    return bor(rshift(x, n), lshift(x, 32 - n))
end
local H0 = {
    0x6a09e667,
    0xbb67ae85,
    0x3c6ef372,
    0xa54ff53a,
    0x510e527f,
    0x9b05688c,
    0x1f83d9ab,
    0x5be0cd19
}
local K = {
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
}
local function preproc(msg)
    local msg_len = #msg
    local bit_len = msg_len * 8
    msg = msg .. string.char(0x80)
    while (#msg % 64) ~= 56 do
        msg = msg .. string.char(0x00)
    end
    local high = math.floor(bit_len / 2^32)
    local low = bit_len % 2^32
    for i = 3, -1, -1 do
        msg = msg .. string.char(band(rshift(high, i * 8), 0xFF))
    end
    for i = 3, -1, -1 do
        msg = msg .. string.char(band(rshift(low, i * 8), 0xFF))
    end
    return msg
end
local function sha256(msg)
    msg = preproc(msg)
    local H = {unpack(H0)}
    for chunk_start = 1, #msg, 64 do
        local w = {}
        local chunk = msg:sub(chunk_start, chunk_start + 63)
        for i = 1, 16 do
            local j = (i - 1) * 4 + 1
            w[i] = bor(
                lshift(string.byte(chunk, j), 24),
                lshift(string.byte(chunk, j + 1), 16),
                lshift(string.byte(chunk, j + 2), 8),
                string.byte(chunk, j + 3)
            )
        end
        for i = 17, 64 do
            local s0 = bxor(rrotate(w[i - 15], 7), rrotate(w[i - 15], 18), rshift(w[i - 15], 3))
            local s1 = bxor(rrotate(w[i - 2], 17), rrotate(w[i - 2], 19), rshift(w[i - 2], 10))
            w[i] = norm(w[i - 16] + s0 + w[i - 7] + s1)
        end
        local a,b,c,d,e,f,g,h = H[1],H[2],H[3],H[4],H[5],H[6],H[7],H[8]
        for i = 1, 64 do
            local S1 = bxor(rrotate(e,6), rrotate(e,11), rrotate(e,25))
            local ch = bxor(band(e,f), band(bnot(e),g))
            local temp1 = norm(h + S1 + ch + K[i] + w[i])
            local S0 = bxor(rrotate(a,2), rrotate(a,13), rrotate(a,22))
            local maj = bxor(band(a,b), band(a,c), band(b,c))
            local temp2 = norm(S0 + maj)
            h = g
            g = f
            f = e
            e = norm(d + temp1)
            d = c
            c = b
            b = a
            a = norm(temp1 + temp2)
        end
        H[1] = norm(H[1] + a)
        H[2] = norm(H[2] + b)
        H[3] = norm(H[3] + c)
        H[4] = norm(H[4] + d)
        H[5] = norm(H[5] + e)
        H[6] = norm(H[6] + f)
        H[7] = norm(H[7] + g)
        H[8] = norm(H[8] + h)
    end
    local digest = {}
    for i = 1, 8 do
        local h = H[i]
        for j = 3, -1, -1 do
            table.insert(digest, string.char(band(rshift(h, j * 8), 0xFF)))
        end
    end
    return (digest and table.concat(digest):gsub('.', function(c)
        return string.format("%02x", string.byte(c))
    end))
end
