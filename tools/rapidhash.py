"""
Pure Python implementation of rapidhash V3 matching lib/rapidhash.h.
The package published on PyPI is NOT COMPATIBLE with rapidhash.h, do not use it!
This implements the COMPACT + FAST + little-endian configuration.
"""

_MASK64 = (1 << 64) - 1

_RAPID_SECRET = (
    0x2D358DCCAA6C78A5,
    0x8BB84B93962EACC9,
    0x4B33A62ED433D4A3,
    0x4D5A2DA51DE1AA47,
    0xA0761D6478BD642F,
    0xE7037ED1A0B428DB,
    0x90ED1765281C388C,
    0xAAAAAAAAAAAAAAAA,
)


def rapidhash(key: bytes, seed: int = 0) -> int:
    return _rapidhash_internal(key, len(key), seed, _RAPID_SECRET)


def _rapidhash_internal(key: bytes, length: int, seed: int, secret: tuple) -> int:
    seed = (seed ^ _rapid_mix(seed ^ secret[2], secret[1])) & _MASK64
    a = b = 0
    i = length
    o = 0  # offset into key (replaces C pointer advancement)

    if length <= 16:
        if length >= 4:
            seed ^= length
            if length >= 8:
                a = _read64(key, 0)
                b = _read64(key, length - 8)
            else:
                a = _read32(key, 0)
                b = _read32(key, length - 4)
        elif length > 0:
            a = (key[0] << 45) | key[length - 1]
            b = key[length >> 1]
        # else: a = b = 0
    else:
        if length > 112:
            see1 = see2 = see3 = see4 = see5 = see6 = seed
            while True:
                seed = _rapid_mix(_read64(key, o) ^ secret[0], _read64(key, o + 8) ^ seed)
                see1 = _rapid_mix(_read64(key, o + 16) ^ secret[1], _read64(key, o + 24) ^ see1)
                see2 = _rapid_mix(_read64(key, o + 32) ^ secret[2], _read64(key, o + 40) ^ see2)
                see3 = _rapid_mix(_read64(key, o + 48) ^ secret[3], _read64(key, o + 56) ^ see3)
                see4 = _rapid_mix(_read64(key, o + 64) ^ secret[4], _read64(key, o + 72) ^ see4)
                see5 = _rapid_mix(_read64(key, o + 80) ^ secret[5], _read64(key, o + 88) ^ see5)
                see6 = _rapid_mix(_read64(key, o + 96) ^ secret[6], _read64(key, o + 104) ^ see6)
                o += 112
                i -= 112
                if i <= 112:
                    break
            seed ^= see1
            see2 ^= see3
            see4 ^= see5
            seed ^= see6
            see2 ^= see4
            seed ^= see2

        if i > 16:
            seed = _rapid_mix(_read64(key, o) ^ secret[2], _read64(key, o + 8) ^ seed)
            if i > 32:
                seed = _rapid_mix(_read64(key, o + 16) ^ secret[2], _read64(key, o + 24) ^ seed)
                if i > 48:
                    seed = _rapid_mix(_read64(key, o + 32) ^ secret[1], _read64(key, o + 40) ^ seed)
                    if i > 64:
                        seed = _rapid_mix(_read64(key, o + 48) ^ secret[1], _read64(key, o + 56) ^ seed)
                        if i > 80:
                            seed = _rapid_mix(_read64(key, o + 64) ^ secret[2], _read64(key, o + 72) ^ seed)
                            if i > 96:
                                seed = _rapid_mix(_read64(key, o + 80) ^ secret[1], _read64(key, o + 88) ^ seed)

        a = _read64(key, o + i - 16) ^ i
        b = _read64(key, o + i - 8)

    a ^= secret[1]
    b ^= seed
    a, b = _rapid_mum(a, b)
    return _rapid_mix(a ^ secret[7], b ^ secret[1] ^ i)


def _rapid_mum(a: int, b: int) -> tuple[int, int]:
    r = a * b
    return r & _MASK64, (r >> 64) & _MASK64


def _rapid_mix(a: int, b: int) -> int:
    lo, hi = _rapid_mum(a, b)
    return lo ^ hi


def _read64(p: bytes, o: int) -> int:
    return int.from_bytes(p[o : o + 8], "little")


def _read32(p: bytes, o: int) -> int:
    return int.from_bytes(p[o : o + 4], "little")


if __name__ == "__main__":
    # fmt: off
    GOLDEN_VECTORS = [
        # (input_bytes, seed, expected_hash)
        # Length 0
        (b"", 0, 0x0338DC4BE2CECDAE),
        # Length 1-3 (branch: len > 0, len < 4)
        (b"x", 0, 0x8C7DB958EB96E161),
        (b"ab", 0, 0x7B20BA72BB425975),
        (b"abc", 0, 0xCB475BEAFA9C0DA2),
        # Length 4-7 (branch: len >= 4, len < 8)
        (b"test", 0, 0xE37001BD99E69F95),
        (b"hello", 0, 0x2E2D7651B45F7946),
        (b"foobar", 0, 0xD76F53D9BFF5E23C),
        (b"1234567", 0, 0x7F96EC4E212DDEAD),
        # Length 8-15 (branch: len >= 8, len <= 16)
        (b"abcdefgh", 0, 0xAB159E602A29F41F),
        (b"123456789", 0, 0x7E7D033B96B916A1),
        (b"0123456789abcde", 0, 0xE10FCF2AEFA96C98),
        # Length 16
        (b"abcdefghijklmnop", 0, 0xC78AE6A1774ADB1E),
        # Length 17-32 (branch: i > 16)
        (b"abcdefghijklmnopq", 0, 0x00C427C11A4463B8),
        (b"A" * 32, 0, 0xD8D1FE5D9A8244E8),
        # Length 33-48 (branch: i > 32)
        (b"B" * 33, 0, 0x528E5A7CDC93EEEC),
        (b"C" * 48, 0, 0x6316AD51A27DE6B1),
        # Length 49-64 (branch: i > 48)
        (b"D" * 49, 0, 0x1B1D78C987E35534),
        (b"E" * 64, 0, 0xEF38F42355744388),
        # Length 65-80 (branch: i > 64)
        (b"F" * 65, 0, 0xFEC6B752FF22CE35),
        (b"G" * 80, 0, 0x12AD88A8DEC79C77),
        # Length 81-96 (branch: i > 80)
        (b"H" * 81, 0, 0x0355475B6A391EA2),
        (b"I" * 96, 0, 0x424C248A7C19354F),
        # Length 97-112 (branch: i > 96)
        (b"J" * 97, 0, 0x558729732E9831A8),
        (b"K" * 112, 0, 0x08414624C601A09D),
        # Length 113+ (7-way parallel loop, 1 iteration)
        (b"L" * 113, 0, 0x0C2659AF62C90310),
        (b"M" * 128, 0, 0x259C8039B0A2E5D9),
        # Length 225+ (multiple loop iterations)
        (b"N" * 225, 0, 0x15FF3875325DC3A9),
        (b"O" * 300, 0, 0x0544633706BE249D),
        (b"P" * 1000, 0, 0xE35E3294ED93C8DE),
        # Non-zero seeds
        (b"hello", 1, 0xC0D3AF1B0F815A9D),
        (b"hello", 0xDEADBEEFCAFEBABE, 0x0D9EFCF40B618387),
        (b"", 42, 0x9293BA21A570895D),
        (b"abc", 0xFFFFFFFFFFFFFFFF, 0xAC0A982A5654A40D),
        # Phrase
        (b"the quick brown fox jumps over the lazy dog", 0, 0x55889A01CA56B226),
    ]
    # fmt: on

    print(f"Running {len(GOLDEN_VECTORS)} golden vector tests...")
    failures = 0
    for data, seed, expected in GOLDEN_VECTORS:
        got = rapidhash(data, seed)
        if got != expected:
            label = data if len(data) <= 20 else f"{data[:10]}...({len(data)}B)"
            print(f"  FAIL: {label!r} seed={seed:#x}: expected {expected:#018x}, got {got:#018x}")
            failures += 1

    if failures:
        print(f"{failures}/{len(GOLDEN_VECTORS)} tests FAILED")
        raise SystemExit(1)
    print("All tests passed.")
