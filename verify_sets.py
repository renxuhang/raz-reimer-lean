"""Independent explicit-set check of Raz 2017, not a Lean kernel replay."""
import itertools


def check_family(family, images):
    universe = frozenset(range(1, 9))
    all_subsets = [frozenset(c) for k in range(9)
                   for c in itertools.combinations(universe, k)]
    intervals = [{c for c in all_subsets if a <= c <= f}
                 for a, f in zip(family, images)]
    frequencies = [sum(x in a for a in family) for x in universe]
    return {
        "same_length": len(family) == len(images) == 11,
        "distinct_members": len(set(family)) == len(family),
        "distinct_images": len(set(images)) == len(images),
        "ground_set_bounds": all(a <= universe for a in family + images),
        "upward_closed": all(t in images for s in images
                             for t in all_subsets if s <= t),
        "contained_in_image": all(a <= f for a, f in zip(family, images)),
        "disjoint_intervals": all(intervals[i].isdisjoint(intervals[j])
                                  for i in range(11) for j in range(i)),
        "frequencies": frequencies,
        "all_frequencies_five": frequencies == [5] * 8,
        "no_abundant_element": all(2 * count < 11 for count in frequencies),
        "not_union_closed": frozenset([1, 8]) not in family,
    }


def verify():
    u = frozenset(range(1, 9))
    family = list(map(frozenset, [
        range(1, 9), [2, 4, 6, 7, 8], [1, 3, 5, 8], [1, 4, 7, 8],
        [2, 3, 5, 6], [1, 3, 7], [2, 3, 5], [2, 4, 6],
        [4, 5, 6, 7], [8], [1]]))
    images = [u] + [u - {i} for i in range(1, 9)] + [u - {1, 2}, u - {3, 4}]
    result = check_family(family, images)
    if not all(value for key, value in result.items() if key != "frequencies"):
        raise RuntimeError("Explicit-set verification failed: " + str(result))
    bad_frequency = family.copy()
    bad_frequency[9] = frozenset([1, 8])
    duplicate = family.copy()
    duplicate[1] = duplicate[0]
    bad_images = images.copy()
    bad_images[0] = frozenset()
    negative = {
        "added_abundant_element_rejected": not check_family(
            bad_frequency, images)["no_abundant_element"],
        "duplicate_rejected": not check_family(duplicate, images)["distinct_members"],
        "invalid_image_rejected": not check_family(
            family, bad_images)["contained_in_image"],
    }
    if not all(negative.values()):
        raise RuntimeError("A negative control was not rejected")
    return {"checks": result, "negative_controls": negative}


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2))
