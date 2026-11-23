"""Exact finite checks of the three-page split butterfly construction."""
from collections import Counter
import itertools


def delete_bit(word, bit):
    low = word & ((1 << bit) - 1)
    return low | ((word >> (bit + 1)) << bit)


def insert_bit(group, bit, value):
    low = group & ((1 << bit) - 1)
    return low | (value << bit) | ((group >> bit) << (bit + 1))


def band_embedding(k):
    width = 1 << k
    sizes = [width if index % 2 == 0 else width // 2 for index in range(2 * k + 1)]
    positions = {}
    order = 0
    for index, size in enumerate(sizes):
        for side, words in enumerate((range(size), range(size - 1, -1, -1))):
            for word in words:
                positions[index, side, word] = order
                order += 1
    pages = [[], [], []]
    for index, size in enumerate(sizes):
        for word in range(size):
            pages[2].append((positions[index, 0, word], positions[index, 1, word]))
    for bit in range(k):
        left, middle, right = 2 * bit, 2 * bit + 1, 2 * bit + 2
        for word in range(width):
            group = delete_bit(word, bit)
            page = (word >> bit) & 1
            pages[page].append((positions[left, 1, word], positions[middle, 0, group]))
            pages[page].append((positions[middle, 1, group], positions[right, 0, word]))
    return positions, pages


def assert_noncross_matching(page):
    events = {}
    for edge in page:
        lo, hi = edge
        assert lo < hi and lo not in events and hi not in events
        events[lo] = (True, hi)
        events[hi] = (False, hi)
    stack = []
    for idx in sorted(events):
        opening, partner = events[idx]
        if opening:
            stack.append(partner)
        else:
            assert stack.pop() == partner
    assert not stack


def check(k):
    width = 1 << k
    pos, pages = band_embedding(k)
    for page in pages:
        assert_noncross_matching(page)
    edges = set(itertools.chain.from_iterable(pages))
    counts = Counter()
    for src, tgt in itertools.product(range(width), repeat=2):
        word = src
        path = [pos[0, side, word] for side in (0, 1)]
        for bit in range(k):
            middle = 2 * bit + 1
            group = delete_bit(word, bit)
            path += [pos[middle, side, group] for side in (0, 1)]
            word = insert_bit(group, bit, (tgt >> bit) & 1)
            path += [pos[middle + 1, side, word] for side in (0, 1)]
        assert word == tgt and len(path) == len(set(path))
        assert all(e in edges for e in zip(path, path[1:]))
        counts.update(path)
    assert all(counts[idx] == width * (2 if part % 2 else 1)
               for (part, _, _), idx in pos.items())
    print(k, len(pos), [len(page) for page in pages], max(counts.values()), flush=True)


if __name__ == '__main__':
    for k in range(1, 9):
        check(k)
