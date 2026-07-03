#!/usr/bin/env python3
"""
This utility is used to generate a topic name whose preferred subject-ID allocation is identical to that
of the given topic name.
Usage:
    ./topic_hash_collider.py 8378431 abc/def
"""

import random
import string
import sys

from rapidhash import rapidhash  # The package published on PyPI is NOT COMPATIBLE with rapidhash.h! Use local version.

ALPHABET = string.ascii_letters + string.digits
PINNED_SUBJECT_ID_MAX = 2 ** 13 - 1
SUBJECT_ID_MODULUS_MIN = 57203
SUBJECT_ID_MODULUS_MAX = 2 ** 32 - 1 - PINNED_SUBJECT_ID_MAX


def topic_hash(topic_name: str) -> int:
    """Pinning is not handled here."""
    return rapidhash(topic_name.encode())


def preferred_subject_id(modulus: int, h: int) -> int:
    """Assumes zero evictions (hence preferred). Only valid for non-pinned topics."""
    return PINNED_SUBJECT_ID_MAX + 1 + (h % modulus)


def find_subject_id_collision(subject_id_modulus: int, topic_name: str, *, suffix_len: int) -> dict[str, int | str]:
    target_hash = topic_hash(topic_name)
    prefix = topic_name
    target_subject_id = preferred_subject_id(subject_id_modulus, target_hash)
    while True:
        suffix = "".join(random.choice(ALPHABET) for _ in range(suffix_len))
        candidate = prefix + suffix
        candidate_hash = topic_hash(candidate)
        if preferred_subject_id(subject_id_modulus, candidate_hash) == target_subject_id:
            return {
                "original_name": topic_name,
                "original_hash": target_hash,
                "collision_name": candidate,
                "collision_hash": candidate_hash,
            }


def is_prime(n: int) -> bool:
    if (n <= 2) or ((n & 1) == 0):
        return n == 2
    d = 3
    while d <= (n // d):
        if (n % d) == 0:
            return False
        d += 2
    return True


def is_valid_subject_id_modulus(modulus: int) -> bool:
    max_subject_id = PINNED_SUBJECT_ID_MAX + modulus
    broadcast_subject_id = (1 << max_subject_id.bit_length()) - 1
    shard_count = broadcast_subject_id - (max_subject_id + 1)
    return (
        (SUBJECT_ID_MODULUS_MIN <= modulus <= SUBJECT_ID_MODULUS_MAX)
        and is_prime(modulus)
        and (modulus % 4 == 3)
        and (0 < shard_count < modulus)
    )


def main() -> None:
    if len(sys.argv) < 3:
        sys.exit(
            f"""
Usage: {sys.argv[0]} <subject-ID-modulus> <topic-name> [suffix-len]
For subject-ID modulus refer to CY_SUBJECT_ID_MODULUS_32bit etc.
""".strip()
        )
    subject_id_modulus = int(sys.argv[1], 0)
    if not is_valid_subject_id_modulus(subject_id_modulus):
        sys.exit(f"Invalid subject-ID modulus: {subject_id_modulus}")
    original = sys.argv[2]
    try:
        suffix_len = int(sys.argv[3])
    except Exception:
        suffix_len = 16

    c = find_subject_id_collision(subject_id_modulus, original, suffix_len=suffix_len)
    ho = c["original_hash"]
    hc = c["collision_hash"]
    nc = c["collision_name"]
    psid = preferred_subject_id(subject_id_modulus, ho)
    assert psid == preferred_subject_id(subject_id_modulus, hc)
    print(
        f"hash_original:        0x{ho:016x}",
        f"hash_collision:       0x{hc:016x}",
        f"name_original:        {original!r}",
        f"name_collision:       {nc!r}",
        f"preferred_subject_id: 0x{psid:08x}",
        sep="\n",
    )


if __name__ == "__main__":
    main()
