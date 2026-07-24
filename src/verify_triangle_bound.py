#!/usr/bin/env python3
"""Exhaustively audit the finite arithmetic in the local Turan/triangle lemma."""

from __future__ import annotations

import json


def turan4_edges(order: int) -> int:
    quotient, remainder = divmod(order, 4)
    sizes = [quotient + 1] * remainder + [quotient] * (4 - remainder)
    return sum(sizes[i] * sizes[j] for i in range(4) for j in range(i + 1, 4))


def forced_color_edges(order: int) -> int:
    return order * (order - 1) // 2 - turan4_edges(order)


def non_four_partite_penalty(order: int) -> int | None:
    """Extra complement deficit from Kang--Pikhurko for chi > 4."""
    if order <= 6:
        return None
    if order <= 8:
        return 2
    return order // 4 - 1


def profiles(total: int, parts: int, prefix: tuple[int, ...] = ()):
    if parts == 1:
        yield prefix + (total,)
        return
    for first in range(total + 1):
        yield from profiles(total - first, parts - 1, prefix + (first,))


def strengthened_profile_bound(degrees: tuple[int, ...]) -> int:
    """Apply every forced non-4-partite penalty, not merely one of them."""
    orders = [25 - degree for degree in degrees]
    value = sum(forced_color_edges(order) for order in orders)
    mandatory = [order for order in orders if order >= 21]
    if mandatory:
        return value + sum(
            penalty
            for order in mandatory
            if (penalty := non_four_partite_penalty(order)) is not None
        )
    return value + min(
        penalty
        for order in orders
        if (penalty := non_four_partite_penalty(order)) is not None
    )


def main() -> int:
    increments = [forced_color_edges(m + 1) - forced_color_edges(m) for m in range(25)]
    expected_increments = [m // 4 for m in range(25)]
    if increments != expected_increments:
        raise AssertionError("discrete convexity increment formula failed")

    minimum = None
    second = None
    minimizers: list[tuple[int, ...]] = []
    strengthened_minimum = None
    strengthened_minimizers: list[tuple[int, ...]] = []
    count = 0
    for degrees in profiles(25, 5):
        count += 1
        value = sum(forced_color_edges(25 - degree) for degree in degrees)
        strengthened_value = strengthened_profile_bound(degrees)
        if minimum is None or value < minimum:
            second = minimum
            minimum = value
            minimizers = [degrees]
        elif value == minimum:
            minimizers.append(degrees)
        elif second is None or value < second:
            second = value
        if strengthened_minimum is None or strengthened_value < strengthened_minimum:
            strengthened_minimum = strengthened_value
            strengthened_minimizers = [degrees]
        elif strengthened_value == strengthened_minimum:
            strengthened_minimizers.append(degrees)
    if count != 23751 or minimum != 200 or second != 201:
        raise AssertionError("unexpected exhaustive profile result")
    if minimizers != [(5, 5, 5, 5, 5)]:
        raise AssertionError("unexpected equality profile")
    if strengthened_minimum != 204 or strengthened_minimizers != [(5, 5, 5, 5, 5)]:
        raise AssertionError("unexpected non-4-partite strengthened minimum")
    strengthened_types = sorted(
        {tuple(sorted(profile)) for profile in strengthened_minimizers}
    )
    if strengthened_types != [(5, 5, 5, 5, 5)]:
        raise AssertionError("unexpected strengthened equality profiles")
    next_strengthened = min(
        strengthened_profile_bound(degrees)
        for degrees in profiles(25, 5)
        if degrees not in strengthened_minimizers
    )
    next_strengthened_profiles = [
        degrees
        for degrees in profiles(25, 5)
        if strengthened_profile_bound(degrees) == next_strengthened
    ]
    next_strengthened_types = sorted(
        {tuple(sorted(profile)) for profile in next_strengthened_profiles}
    )
    if (
        next_strengthened != 205
        or len(next_strengthened_profiles) != 20
        or next_strengthened_types != [(4, 5, 5, 5, 6)]
    ):
        raise AssertionError("unexpected next strengthened profiles")
    following_strengthened = min(
        strengthened_profile_bound(degrees)
        for degrees in profiles(25, 5)
        if strengthened_profile_bound(degrees) > next_strengthened
    )
    following_strengthened_profiles = [
        degrees
        for degrees in profiles(25, 5)
        if strengthened_profile_bound(degrees) == following_strengthened
    ]
    following_strengthened_types = sorted(
        {tuple(sorted(profile)) for profile in following_strengthened_profiles}
    )
    if (
        following_strengthened != 206
        or len(following_strengthened_profiles) != 50
        or following_strengthened_types
        != [(3, 5, 5, 5, 7), (3, 5, 5, 6, 6)]
    ):
        raise AssertionError("unexpected following strengthened profiles")

    result = {
        "claim": "LOCAL-TURAN-TRIANGLE-BOUND",
        "degree_profiles_checked": count,
        "equality_profiles": [list(profile) for profile in minimizers],
        "forced_edge_function_0_to_25": [forced_color_edges(m) for m in range(26)],
        "minimum_local_count": minimum,
        "minimum_unbalanced_local_count": second,
        "non_four_partite_penalty_0_to_25": [
            non_four_partite_penalty(order) for order in range(26)
        ],
        "strengthened_equality_profile_types": [
            list(profile) for profile in strengthened_types
        ],
        "strengthened_minimum_local_count": strengthened_minimum,
        "strengthened_ordered_profiles": len(strengthened_minimizers),
        "next_strengthened_local_count": next_strengthened,
        "next_strengthened_ordered_profiles": len(next_strengthened_profiles),
        "next_strengthened_profile_types": [
            list(profile) for profile in next_strengthened_types
        ],
        "following_strengthened_local_count": following_strengthened,
        "following_strengthened_ordered_profiles": len(
            following_strengthened_profiles
        ),
        "following_strengthened_profile_types": [
            list(profile) for profile in following_strengthened_types
        ],
        "scope": "finite arithmetic audit supporting the human proof; not a resolution",
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
