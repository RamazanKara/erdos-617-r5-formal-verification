#!/usr/bin/env python3
"""Exhaustively enumerate the order-16 6-Ore classes relevant to E031."""

from __future__ import annotations

import collections
import itertools
import json
from collections.abc import Iterable, Iterator

Graph = frozenset[tuple[int, int]]


def complete_graph(order: int) -> Graph:
    return frozenset(itertools.combinations(range(order), 2))


def graph6_encode(graph: Graph, order: int) -> str:
    if not 0 <= order <= 62:
        raise ValueError("compact graph6 encoder supports orders zero through 62")
    bits = [
        int((left, right) in graph)
        for right in range(1, order)
        for left in range(right)
    ]
    bits.extend([0] * (-len(bits) % 6))
    payload = "".join(
        chr(63 + sum(bits[index + offset] << (5 - offset) for offset in range(6)))
        for index in range(0, len(bits), 6)
    )
    return chr(order + 63) + payload


def graph6_decode(encoded: str) -> tuple[int, Graph]:
    if not encoded or not 63 <= ord(encoded[0]) <= 125:
        raise ValueError("unsupported graph6 order prefix")
    order = ord(encoded[0]) - 63
    values = [ord(character) - 63 for character in encoded[1:]]
    if any(not 0 <= value < 64 for value in values):
        raise ValueError("malformed graph6 payload")
    bits = [
        (value >> shift) & 1 for value in values for shift in range(5, -1, -1)
    ]
    required = order * (order - 1) // 2
    if len(bits) != (required + 5) // 6 * 6 or any(bits[required:]):
        raise ValueError("noncanonical graph6 payload length or padding")
    graph = frozenset(
        (left, right)
        for bit, (right, left) in zip(
            bits[:required],
            ((right, left) for right in range(1, order) for left in range(right)),
            strict=True,
        )
        if bit
    )
    return order, graph


def adjacency(graph: Graph, order: int) -> tuple[frozenset[int], ...]:
    result = [set() for _ in range(order)]
    for left, right in graph:
        result[left].add(right)
        result[right].add(left)
    return tuple(frozenset(neighbors) for neighbors in result)


def ore_compositions(edge_graph: Graph, edge_order: int, split_graph: Graph, split_order: int) -> Iterator[Graph]:
    """Yield every labeled DHGO composition, including both ordered split parts."""

    split_adjacency = adjacency(split_graph, split_order)
    for left, right in sorted(edge_graph):
        edge_remainder = set(edge_graph)
        edge_remainder.remove((left, right))
        for split in range(split_order):
            neighbors = tuple(sorted(split_adjacency[split]))
            for mask in range(1, (1 << len(neighbors)) - 1):
                first = {
                    point for index, point in enumerate(neighbors) if mask & (1 << index)
                }
                mapping = {}
                next_vertex = edge_order
                for point in range(split_order):
                    if point == split:
                        continue
                    mapping[point] = next_vertex
                    next_vertex += 1
                composed = set(edge_remainder)
                for first_point, second_point in split_graph:
                    if split not in (first_point, second_point):
                        composed.add(
                            tuple(sorted((mapping[first_point], mapping[second_point])))
                        )
                for point in neighbors:
                    composed.add((left if point in first else right, mapping[point]))
                if next_vertex != edge_order + split_order - 1:
                    raise AssertionError("DHGO composition order changed")
                yield frozenset(tuple(sorted(edge)) for edge in composed)


def refinement_signature(graph: Graph, order: int) -> tuple[object, ...]:
    adj = adjacency(graph, order)
    colors = [len(neighbors) for neighbors in adj]
    while True:
        signatures = [
            (colors[point], tuple(sorted(colors[other] for other in adj[point])))
            for point in range(order)
        ]
        palette = {signature: index for index, signature in enumerate(sorted(set(signatures)))}
        refined = [palette[signature] for signature in signatures]
        if refined == colors:
            break
        colors = refined
    classes = collections.Counter(colors)
    cross = collections.Counter()
    for left, right in graph:
        cross[tuple(sorted((colors[left], colors[right])))] += 1
    return (
        tuple(sorted(len(neighbors) for neighbors in adj)),
        tuple(sorted(classes.items())),
        tuple(sorted(cross.items())),
    )


def isomorphic(first: Graph, second: Graph, order: int) -> bool:
    """Exact individualization/refinement isomorphism check."""

    if len(first) != len(second):
        return False
    first_adjacency = adjacency(first, order)
    second_adjacency = adjacency(second, order)
    if sorted(map(len, first_adjacency)) != sorted(map(len, second_adjacency)):
        return False

    def search(first_colors: tuple[int, ...], second_colors: tuple[int, ...]) -> bool:
        while True:
            signatures = []
            for adj, colors in (
                (first_adjacency, first_colors),
                (second_adjacency, second_colors),
            ):
                signatures.extend(
                    (colors[point], tuple(sorted(colors[other] for other in adj[point])))
                    for point in range(order)
                )
            palette = {
                signature: index for index, signature in enumerate(sorted(set(signatures)))
            }
            new_first = tuple(
                palette[
                    (
                        first_colors[point],
                        tuple(sorted(first_colors[other] for other in first_adjacency[point])),
                    )
                ]
                for point in range(order)
            )
            new_second = tuple(
                palette[
                    (
                        second_colors[point],
                        tuple(sorted(second_colors[other] for other in second_adjacency[point])),
                    )
                ]
                for point in range(order)
            )
            if collections.Counter(new_first) != collections.Counter(new_second):
                return False
            if new_first == first_colors and new_second == second_colors:
                break
            first_colors, second_colors = new_first, new_second

        color_classes = collections.defaultdict(list)
        for point, color in enumerate(first_colors):
            color_classes[color].append(point)
        if all(len(points) == 1 for points in color_classes.values()):
            inverse = {color: point for point, color in enumerate(second_colors)}
            mapping = {point: inverse[color] for point, color in enumerate(first_colors)}
            return all(
                ((left, right) in first)
                == (tuple(sorted((mapping[left], mapping[right]))) in second)
                for left, right in itertools.combinations(range(order), 2)
            )

        chosen_color, chosen_points = min(
            (
                (color, points)
                for color, points in color_classes.items()
                if len(points) > 1
            ),
            key=lambda item: (len(item[1]), item[0]),
        )
        first_point = chosen_points[0]
        second_points = [
            point for point, color in enumerate(second_colors) if color == chosen_color
        ]
        individualized = max(max(first_colors), max(second_colors)) + 1
        for second_point in second_points:
            next_first = list(first_colors)
            next_second = list(second_colors)
            next_first[first_point] = individualized
            next_second[second_point] = individualized
            if search(tuple(next_first), tuple(next_second)):
                return True
        return False

    first_initial = tuple(len(neighbors) for neighbors in first_adjacency)
    second_initial = tuple(len(neighbors) for neighbors in second_adjacency)
    return search(first_initial, second_initial)


def deduplicate(graphs: Iterable[Graph], order: int) -> tuple[tuple[Graph, ...], tuple[int, ...], int]:
    exact = sorted(set(graphs), key=lambda graph: tuple(sorted(graph)))
    representatives: list[Graph] = []
    multiplicities: list[int] = []
    buckets: dict[tuple[object, ...], list[int]] = collections.defaultdict(list)
    for graph in exact:
        signature = refinement_signature(graph, order)
        matches = [
            index
            for index in buckets[signature]
            if isomorphic(graph, representatives[index], order)
        ]
        if len(matches) > 1:
            raise AssertionError("isomorphism representatives overlap")
        if matches:
            multiplicities[matches[0]] += 1
        else:
            buckets[signature].append(len(representatives))
            representatives.append(graph)
            multiplicities.append(1)
    for first, second in itertools.combinations(range(len(representatives)), 2):
        if isomorphic(representatives[first], representatives[second], order):
            raise AssertionError("pairwise nonisomorphic representatives merged incorrectly")
    return tuple(representatives), tuple(multiplicities), len(exact)


def colorable(graph: Graph, order: int, colors: int, omitted: int | None = None) -> bool:
    adj = adjacency(graph, order)
    vertices = set(range(order))
    if omitted is not None:
        vertices.remove(omitted)
    assigned: dict[int, int] = {}

    def search() -> bool:
        if len(assigned) == len(vertices):
            return True
        uncolored = vertices - assigned.keys()
        point = max(
            uncolored,
            key=lambda candidate: (
                len({assigned[other] for other in adj[candidate] if other in assigned}),
                len(adj[candidate] & vertices),
                -candidate,
            ),
        )
        forbidden = {assigned[other] for other in adj[point] if other in assigned}
        for color in range(colors):
            if color in forbidden:
                continue
            assigned[point] = color
            if search():
                return True
            del assigned[point]
        return False

    return search()


def semantic_profile(graph: Graph, order: int = 16) -> dict[str, object]:
    adj = adjacency(graph, order)
    independent_four = sum(
        not any(edge in graph for edge in itertools.combinations(subset, 2))
        for subset in itertools.combinations(range(order), 4)
    )
    clique_six = sum(
        all(edge in graph for edge in itertools.combinations(subset, 2))
        for subset in itertools.combinations(range(order), 6)
    )
    private_counts = []
    for left, right in sorted(graph):
        available = [point for point in range(order) if point not in (left, right)]
        private_counts.append(
            sum(
                all(
                    tuple(sorted(edge)) not in graph
                    for edge in (
                        (left, first),
                        (left, second),
                        (right, first),
                        (right, second),
                        (first, second),
                    )
                )
                for first, second in itertools.combinations(available, 2)
            )
        )
    return {
        "edge_count": len(graph),
        "degrees": tuple(sorted(map(len, adj))),
        "independent_four_sets": independent_four,
        "clique_six_sets": clique_six,
        "critical_edges": sum(count > 0 for count in private_counts),
        "private_pair_total": sum(private_counts),
        "minimum_private_pairs": min(private_counts),
        "five_colorable": colorable(graph, order, 5),
        "all_deletions_five_colorable": all(
            colorable(graph, order, 5, omitted) for omitted in range(order)
        ),
    }


def enumerate_classes() -> tuple[tuple[Graph, ...], tuple[dict[str, object], ...], dict[str, object]]:
    k6 = complete_graph(6)
    raw11 = tuple(ore_compositions(k6, 6, k6, 6))
    classes11, multiplicities11, exact11 = deduplicate(raw11, 11)
    raw16 = []
    for graph in classes11:
        raw16.extend(ore_compositions(k6, 6, graph, 11))
        raw16.extend(ore_compositions(graph, 11, k6, 6))
    classes16, multiplicities16, exact16 = deduplicate(raw16, 16)
    profiles = tuple(semantic_profile(graph) for graph in classes16)
    survivors = tuple(
        graph
        for graph, profile in zip(classes16, profiles, strict=True)
        if profile["edge_count"] == 43
        and min(profile["degrees"]) >= 5
        and profile["independent_four_sets"] == 0
        and profile["clique_six_sets"] == 0
        and profile["critical_edges"] == 43
        and profile["five_colorable"] is False
        and profile["all_deletions_five_colorable"] is True
    )
    survivor_profiles = tuple(semantic_profile(graph) for graph in survivors)
    metadata = {
        "raw11": len(raw11),
        "exact11": exact11,
        "classes11": len(classes11),
        "multiplicities11": multiplicities11,
        "raw16": len(raw16),
        "exact16": exact16,
        "classes16": len(classes16),
        "multiplicities16": multiplicities16,
        "survivors": len(survivors),
    }
    return survivors, survivor_profiles, metadata


def main() -> int:
    survivors, profiles, metadata = enumerate_classes()
    print("MINORITY63-Q16-ORE-ENUMERATION-PASS " + json.dumps(metadata, sort_keys=True))
    for index, (graph, profile) in enumerate(zip(survivors, profiles, strict=True), start=1):
        print(
            json.dumps(
                {
                    "index": index,
                    "graph6": graph6_encode(graph, 16),
                    "edges": [list(edge) for edge in sorted(graph)],
                    "profile": profile,
                },
                sort_keys=True,
            )
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
