#!/usr/bin/env python3
"""
This utility is used to generate a topic name whose preferred subject-ID allocation is identical to that
of the given topic name.
Usage:
    ./topic_hash_collider.py /abc/def
"""

import sys
import random
import string
from rapidhash import rapidhash

ALPHABET = string.ascii_letters + string.digits
PINNED_SUBJECT_ID_MAX = 2**13 - 1


def topic_hash(topic_name: str) -> int:
    if len(topic_name) == 5 and topic_name.startswith("#"):
        try:
            numeric = int(topic_name[1:], 16)
        except ValueError:
            pass
        else:
            if 0 <= numeric <= PINNED_SUBJECT_ID_MAX:
                return numeric
    return rapidhash(topic_name.encode())


def preferred_subject_id(modulus: int, h: int) -> int:
    if h <= PINNED_SUBJECT_ID_MAX:  # This is a pinned topic.
        return h
    return PINNED_SUBJECT_ID_MAX + h % modulus


def find_subject_id_collision(subject_id_modulus: int, topic_name: str, *, suffix_len: int) -> dict[str, int | str]:
    target_hash = topic_hash(topic_name)
    if target_hash <= PINNED_SUBJECT_ID_MAX:
        raise ValueError(f"Pinned topics are collision-free by design: {topic_name!r}")
    prefix = topic_name
    target_subject_id = preferred_subject_id(subject_id_modulus, target_hash)
    while True:
        suffix = ''.join(random.choice(ALPHABET) for _ in range(suffix_len))
        candidate = prefix + suffix
        candidate_hash = topic_hash(candidate)
        if preferred_subject_id(subject_id_modulus, candidate_hash) == target_subject_id:
            return {
                "original_name": topic_name,
                "original_hash": target_hash,
                "collision_name": candidate,
                "collision_hash": candidate_hash,
            }


def main() -> None:
    if len(sys.argv) < 3:
        sys.exit(f"Usage: {sys.argv[0]} <subject-ID-modulus> <topic-name> [suffix-len]")
    subject_id_modulus = int(sys.argv[1], 0)
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
        f"hash_original:  0x{ho:016x}",
        f"hash_collision: 0x{hc:016x}",
        f"name_collision: {nc!r}",
        f"preferred_subject_id: 0x{psid:08x}",
        sep="\n",
    )


if __name__ == "__main__":
    main()
