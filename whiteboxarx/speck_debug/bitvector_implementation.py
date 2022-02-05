"""Unprotected implementation of Speck with bitvector operations."""


def get_encryption(speck_instance, rounds, round_keys):
    """Return an instance of the Speck family."""
    default_rounds = speck_instance.default_rounds
    n = speck_instance.ws
    alpha = speck_instance.alpha
    beta = speck_instance.beta

    if rounds is None:
        rounds = default_rounds

    assert 1 <= rounds <= default_rounds

    # def RotateLeft(val, r):
    #     width = n
    #     mask = 2 ** width - 1
    #     r = r % width
    #     return ((val << r) & mask) | ((val & mask) >> (width - r))
    #
    # def RotateRight(val, r):
    #     width = n
    #     mask = 2 ** width - 1
    #     r = r % width
    #     return ((val & mask) >> r) | (val << (width - r) & mask)
    #
    # def BvAdd(x, y):
    #     return (x + y) % (2 ** n)

    # def rf(x, y, k):
    #     x = BvAdd(RotateRight(x, alpha), y) ^ k
    #     y = RotateLeft(y, beta) ^ x
    #     return x, y
    #
    # def SpeckEncryption(x, y):
    #     for i in range(rounds):
    #         x, y = rf(x, y, round_keys[i])
    #     return x, y

    # def rf(x, y, k, last_round):
    #     x, y = RotateRight(x, alpha), y
    #     x, y = BvAdd(x, y), y
    #     x, y = x ^ k, RotateLeft(y, beta)
    #     x, y = x, x ^ y
    #     return x, y

    # def SpeckEncryption(x, y):
    #     x, y = RotateRight(x, alpha), y
    #     x, y = BvAdd(x, y), y
    #
    #     for i in range(rounds):
    #         if i not in [rounds - 2, rounds - 1]:
    #             x, y = x ^ round_keys[i], RotateLeft(y, beta)
    #             x, y = x, x ^ y
    #             x, y = RotateRight(x, alpha), y
    #             x, y = BvAdd(x, y), y
    #         elif i == rounds - 2:
    #             x, y = x ^ round_keys[i], RotateLeft(y, beta)
    #             x, y = x, x ^ y
    #             x, y = RotateRight(x, alpha), y
    #             x, y = BvAdd(x, y), y
    #             x, y = x ^ round_keys[i+1], RotateLeft(y, beta)
    #             x, y = x, x ^ y
    #         else:
    #             continue
    #     return x, y

    def Identity_RotateLeft(left_operand, val):
        r = beta
        width = n
        mask = 2 ** width - 1
        r = r % width
        return left_operand, ((val << r) & mask) | ((val & mask) >> (width - r))

    def RotateRight_Identity(val, right_operand):
        r = alpha
        width = n
        mask = 2 ** width - 1
        r = r % width
        return ((val & mask) >> r) | (val << (width - r) & mask), right_operand

    def PermutedBvAdd(x, y):
        x, y = (x + y) % (2 ** n), y
        return x, y

    def Identity_Xor(x, y):
        return x, x ^ y

    def SpeckEncryption(x, y):
        x, y = RotateRight_Identity(x, y)
        x, y = PermutedBvAdd(x, y)

        for i in range(rounds):
            if i not in [rounds - 2, rounds - 1]:
                x, y = Identity_RotateLeft(x ^ round_keys[i], y)
                x, y = Identity_Xor(x, y)
                x, y = RotateRight_Identity(x, y)
                x, y = PermutedBvAdd(x, y)
            elif i == rounds - 2:
                x, y = Identity_RotateLeft(x ^ round_keys[i], y)
                x, y = Identity_Xor(x, y)
                x, y = RotateRight_Identity(x, y)
                x, y = PermutedBvAdd(x, y)
                x, y = Identity_RotateLeft(x ^ round_keys[i+1], y)
                x, y = Identity_Xor(x, y)
            else:
                continue
        return x, y

    return SpeckEncryption


if __name__ == '__main__':
    from whiteboxarx.speck_debug.test_vectors import run_test_vectors
    run_test_vectors(get_encryption)
