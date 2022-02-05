from whiteboxarx.speck import (
    AllSpeckInstances,
    Speck_8_16, Speck_32_64, Speck_48_96, Speck_64_96, Speck_64_128, Speck_128_256
)


def run_test_vectors(get_encryption):
    for speck_instance in AllSpeckInstances:
        if speck_instance == Speck_8_16:
            plaintext = (1, 2)
            key = (1, 2, 3, 4)
            encryption_function = get_encryption(speck_instance, None, key)
            ciphertext = encryption_function(*plaintext)
            assert ciphertext == (4, 8)
        elif speck_instance == Speck_32_64:
            plaintext = (0x6574, 0x694c)
            key = (0x1918, 0x1110, 0x0908, 0x0100)
            encryption_function = get_encryption(speck_instance, None, key)
            ciphertext = encryption_function(*plaintext)
            assert ciphertext == (0xa868, 0x42f2)
        elif speck_instance == Speck_48_96:
            plaintext = (0x6d2073, 0x696874)
            key = (0x1a1918, 0x121110, 0x0a0908, 0x020100)
            encryption_function = get_encryption(speck_instance, None, key)
            ciphertext = encryption_function(*plaintext)
            assert ciphertext == (0x735e10, 0xb6445d)
        elif speck_instance == Speck_64_96:
            plaintext = (0x74614620, 0x736e6165)
            key = (0x13121110, 0x0b0a0908, 0x03020100)
            encryption_function = get_encryption(speck_instance, None, key)
            ciphertext = encryption_function(*plaintext)
            assert ciphertext == (0x9f7952ec, 0x4175946c)
        elif speck_instance == Speck_64_128:
            plaintext = (0x3b726574, 0x7475432d)
            key = (0x1b1a1918, 0x13121110, 0x0b0a0908, 0x03020100)
            encryption_function = get_encryption(speck_instance, None, key)
            ciphertext = encryption_function(*plaintext)
            assert ciphertext == (0x8c6fa548, 0x454e028b)
        elif speck_instance == Speck_128_256:
            plaintext = (0x65736f6874206e49, 0x202e72656e6f6f70)
            key = (0x1f1e1d1c1b1a1918, 0x1716151413121110, 0x0f0e0d0c0b0a0908, 0x0706050403020100)
            encryption_function = get_encryption(speck_instance, None, key)
            ciphertext = encryption_function(*plaintext)
            assert ciphertext == (0x4109010405c0f53e, 0x4eeeb48d9c188f43)
