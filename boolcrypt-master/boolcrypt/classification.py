"""Classify a list of permutations of the same bitsize according to given properties."""
import collections

from boolcrypt.utilities import (
    int2vector, get_differential_uniformity, get_linearity, get_bitsize,
    get_smart_print, get_all_algebraic_degrees, lut2anf, lut2hex_string
)
from boolcrypt.equivalence import (
    get_lut_inversion, get_number_self_le, get_number_self_ae,
)
from boolcrypt.functionalequations import (
    find_nondiagonal_ase, find_noninvertible_ase, find_horizontal_decomposition,
)

import sage.all

from sage.crypto.sboxes import SBox as SageSBox

GF = sage.all.GF


_Properties = collections.namedtuple(
    'Properties',
    ['diff', 'lin', 'maxD', 'minD', 'linC',
     'linS', 'linSE', 'affSE', 'addSE', 'niSE', 'ndSE',
     'dec']
)


class Properties(_Properties):
    """Abstract class that list the cryptographic properties to classify a list of permutations.

    Subclasses override the bitsize n of the functions and
    whether to ignore the self-equivalence properties ignore_se
    and the decomposition properties ignore_dec.

    An instance of a subclass represents the properties of a particular permutations.

    Base cryptographic properties:
    - diff: differential uniformity (log2)
    - lin: linearity (log2)
    - maxD: high (max) degree
    - minD: low (min) degree
    - linC: an n-bit hex value with i-th bit active if i-th component is linear
    - linS: an n-bit hex value with i-th bit active if i-th component has a linear structure

    Self-equivalence properties:
    - linSE: number of linear self-equivalences (log2)
    - affSE: number of affine self-equivalences (log2)
    - addSE: number of additive self-equivalences (log2)
    - niSE: whether has non-invertible affine self-equivalences
    - ndSE: whether has non-diagonal affine self-equivalence when concatenated with itself

    Decomposition property:
    - dec: an n-bit hex value with i-th bit active if is affine equivalent to
    F(x1,..,xi)|G(x{i+1),...)

    """
    __slots__ = ()

    @classmethod
    def get_properties(cls, lut, verbose=False, **sat_args):
        n = cls.n
        assert n == get_bitsize(lut)
        diff = get_differential_uniformity(lut)
        lin = get_linearity(lut)

        all_degs = get_all_algebraic_degrees(lut)
        max_deg, min_deg = max(all_degs), min(all_degs)

        lc = int("0b" + "".join(reversed(["1" if deg <= 1 else "0" for deg in all_degs])), base=2)

        ls_hasls = ["0" for _ in range(2 ** n)]
        ls_comp2numls = collections.Counter()
        sage_sbox = SageSBox(lut)
        sage_sbox_ls = sage_sbox.linear_structures()
        for (b, _, _) in sage_sbox_ls:
            ls_hasls[b] = "1"
            ls_comp2numls[b] += 1
        ls_hasls = int("0b" + "".join(reversed(ls_hasls)), base=2)
        # properties.ls = ls_hasls, ls_comp2numls is for dec

        if verbose is False:
            sat_args["filename"] = False

        if not cls.ignore_se or not cls.ignore_dec:
            anf = lut2anf(lut)
            ls_matrix = sage.all.matrix(GF(2), ncols=n, entries=[int2vector(i, n) for i in ls_comp2numls])
            ls_matrix_rank = ls_matrix.rank()

        if not cls.ignore_se:
            linSE = get_number_self_le(lut)
            affSE = get_number_self_ae(lut, verbose=verbose)

            ddt = sage_sbox.difference_distribution_table().list()
            addSE = ddt.count(ddt[0])

            # if S does not have LS, S||S cannot have non-diagonal SE
            if ls_hasls == 0:
                ndSE = False
            else:
                ndSE = find_nondiagonal_ase(anf, anf, verbose=verbose, **sat_args)
                ndSE = ndSE is not None

            # assume B S = S A, for non-zero non-invertible (A, B)
            # This is equivalent to (S_{i_1}(x), ..., S_{i_n}(x)) = S(x_1, ..., x_r, 0)
            # for some S_{i_1}, ..., S_{i_n} components (non-necessarily different)
            # Thus, at least one component must have an ls.
            # Exactly, r independent components have 2^{n-r} LS
            aux = all(min([numls for comp, numls in ls_comp2numls.most_common(r)]) + 1 < 2 ** (n - r)
                      for r in (1, ls_matrix_rank))
            if ls_hasls == 0 or aux:
                niSE = False
            else:
                niSE = find_noninvertible_ase(anf, verbose=verbose, **sat_args)
                niSE = niSE is not None
        else:
            linSE = None
            affSE = None
            addSE = None
            niSE = None
            ndSE = None

        if not cls.ignore_dec:
            decompositions = ["0" for _ in range(n)]

            # at least n independent components must have LS (1)
            # AND one component must have more than 2^(n-1) LS
            #     n-1 component must have more than 2^(1) LS (True since (1))
            # + 1 since SBox.linear_structures() does not count the LS (0, 0)
            if ls_matrix_rank < n or max(ls_comp2numls.values()) + 1 < 2 ** (n - 1):
                pass
            else:
                result = find_horizontal_decomposition(anf, 1, 1, verbose=verbose, **sat_args)
                if result is not None:
                    decompositions[1] = "1"
                    decompositions[n - 1] = "1"

            # at least n independent components must have LS (1)
            # AND two components must have more than 2^(n-2) LS
            #     n-2 components must have more than 2^(2) LS
            if (n >= 4 or max_deg <= 1) and (ls_matrix_rank < n or
                    any(num_ls + 1 < 2 ** (n - 2) for comp, num_ls in ls_comp2numls.most_common(2)) or
                    any(num_ls + 1 < 2 ** 2 for comp, num_ls in ls_comp2numls.most_common(n))):
                pass
            else:
                result = find_horizontal_decomposition(anf, 1, 2, verbose=verbose, **sat_args)
                if result is not None:
                    decompositions[2] = "1"
                    decompositions[n - 2] = "1"

            for i in range(3, int(n / 2)):
                result = find_horizontal_decomposition(anf, 1, i, verbose=verbose, **sat_args)
                if result is not None:
                    decompositions[i] = "1"
                    decompositions[n - i] = "1"

            dec = int("0b" + "".join(reversed(decompositions)), base=2)
        else:
            dec = None

        return cls(
            diff=diff,
            lin=lin,
            maxD=int(max_deg),
            minD=int(min_deg),
            linC=hex(lc),
            linS=hex(ls_hasls),
            #
            linSE=linSE,
            affSE=affSE,
            addSE=addSE,
            niSE=niSE,
            ndSE=ndSE,
            dec=hex(dec) if dec is not None else None
        )

    @classmethod
    def get_properties_identity(cls):
        # identity properties are computed for checking
        n = cls.n
        lut = [i for i in range(2 ** n)]
        diff = get_differential_uniformity(lut)
        lin = get_linearity(lut)

        all_degs = get_all_algebraic_degrees(lut)
        max_deg, min_deg = max(all_degs), min(all_degs)

        lc = int("0b" + "".join(reversed(["1" if deg <= 1 else "0" for deg in all_degs])), base=2)

        ls = ["0" for _ in range(2 ** n)]
        for (b, _, _) in SageSBox(lut).linear_structures():
            ls[b] = "1"
        ls = int("0b" + "".join(reversed(ls)), base=2)

        dec = ["1" for _ in range(n)]
        dec[0], dec[n - 1] = "0", "0"
        dec = int("0b" + "".join(reversed(dec)), base=2)

        return cls(
            diff=diff,
            lin=lin,
            maxD=int(max_deg),
            minD=int(min_deg),
            linC=hex(lc),
            linS=hex(ls),
            #
            linSE=sage.all.GL(n, GF(2)).cardinality(),
            affSE=sage.all.GL(n, GF(2)).cardinality() * 2 ** n,
            addSE=2 ** n,
            niSE=True,
            ndSE=True,
            dec=hex(dec),
        )

    @classmethod
    def get_properties_inversion(cls, verbose=False, **sat_args):
        n = cls.n
        lut = get_lut_inversion(n)

        # 3-bit inversion is different than 4-bit inversion
        if n == 3:
            return cls.get_properties(lut, verbose=verbose, **sat_args)

        diff = get_differential_uniformity(lut)
        lin = get_linearity(lut)

        all_degs = get_all_algebraic_degrees(lut)
        max_deg, min_deg = max(all_degs), min(all_degs)

        lc = int("0b" + "".join(reversed(["1" if deg <= 1 else "0" for deg in all_degs])), base=2)

        ls = ["0" for _ in range(2 ** n)]
        for (b, _, _) in SageSBox(lut).linear_structures():
            ls[b] = "1"
        ls = int("0b" + "".join(reversed(ls)), base=2)

        dec = ["0" for _ in range(n)]
        dec = int("0b" + "".join(reversed(dec)), base=2)

        return cls(
            diff=diff,
            lin=lin,
            maxD=int(max_deg),
            minD=int(min_deg),
            linC=hex(lc),
            linS=hex(ls),
            #
            linSE=n * (2 ** n - 1),
            affSE=n * (2 ** n - 1),
            addSE=1,  # 0 -> 0
            niSE=False,
            ndSE=False,
            dec=hex(dec),
        )

    @classmethod
    def get_property_names(cls):
        fields = []
        for field in cls._fields:
            if cls.ignore_se and field in ['linSE', 'affSE', 'addSE', 'niSE', 'ndSE']:
                continue
            elif cls.ignore_dec and field in ['dec']:
                continue
            fields.append(field)
        return ",".join(fields)

    def __str__(self):
        args = []
        for x, field in zip(self, self._fields):
            if self.ignore_se and field in ['linSE', 'affSE', 'addSE', 'niSE', 'ndSE']:
                continue
            elif self.ignore_dec and field in ['dec']:
                continue
            args.append(x)

        return ','.join([str(x) for x in args])


def get_properties(bitsize, ignore_se_properties=True, ignore_dec_properties=True):
    """Return a subclass of Properties used in classify_sboxes_properties().

    Return a subclass of Properties where it is fixed the bitsize and whether
    to include self-equivalence and decomposition properties.

        >>> Prop3b = get_properties(3, False, False)
        >>> Prop3b.get_property_names()
        'diff,lin,maxD,minD,linC,linS,linSE,affSE,addSE,niSE,ndSE,dec'
        >>> str(Prop3b.get_properties_identity())
        '8,4,1,1,0x7f,0xfe,168,1344,8,True,True,0x2'
        >>> str(Prop3b.get_properties_inversion())  # doctest: +SKIP
        '2,2,2,2,0x0,0xfe,21,168,1,False,False,0x0'
        >>> Prop4b = get_properties(4)
        >>> Prop4b.get_property_names()
        'diff,lin,maxD,minD,linC,linS'
        >>> str(Prop4b.get_properties_identity())
        '16,8,1,1,0x7fff,0xfffe'
        >>> str(Prop4b.get_properties_inversion())
        '4,4,3,3,0x0,0x0'

    """
    assert bitsize >= 3

    class PropertiesFixedBitsize(Properties):
        n = bitsize
        ignore_se = ignore_se_properties
        ignore_dec = ignore_dec_properties

    return PropertiesFixedBitsize


def classify_sboxes(candidates, properties, add_identity_row=False, add_inversion_row=False,
                    verbose=False, filename=None, **sat_args):
    """Classify a list of permutations of the same bitsize according to given properties.

    Returns a CSV-like list, where each row is the list of properties of an S-box.
    The first row is the header with the names of each column property.

    The argument properties can be obtained from get_properties().

    If add_identity_row=True, the properties of the identity function are added
    after the header.
    If add_inversion_row=True, the properties of the inversion function are added
    after the header.

        >>> from boolcrypt.sboxes import affine_3b_classes
        >>> Prop3b = get_properties(3, ignore_se_properties=False, ignore_dec_properties=False)
        >>> classify_sboxes(affine_3b_classes, Prop3b)  # doctest: +SKIP
        lut,diff,lin,maxD,minD,linC,linS,linSE,affSE,addSE,niSE,ndSE,dec
        01234567,8,4,1,1,0x7f,0xfe,168,1344,8,True,True,0x6
        01234576,8,4,2,1,0x2a,0xfe,24,192,2,True,True,0x0
        01234675,4,4,2,1,0x8,0xfe,12,96,1,True,False,0x0
        01243675,2,2,2,2,0x0,0xfe,21,168,1,False,False,0x0
        >>> from boolcrypt.sboxes import high_se_4bit_2deg_sboxes
        >>> Prop4b = get_properties(4, ignore_se_properties=False, ignore_dec_properties=False)
        >>> classify_sboxes(high_se_4bit_2deg_sboxes, Prop4b, add_identity_row=True)  # doctest: +SKIP
        lut,diff,lin,maxD,minD,linC,linS,linSE,affSE,addSE,niSE,ndSE,dec
        0123456789abcdef,16,8,1,1,0x7fff,0xfffe,20160,322560,16,True,True,0x6
        6512304789abcdef,8,8,2,1,0x80,0xfffe,8,448,1,True,False,0x0
        40132567c89badef,16,8,2,1,0x80,0xfffe,3,336,2,True,True,0x0
        40623517a98bcdef,16,8,2,1,0x80,0xfffe,4,384,2,True,True,0x0
        2013645789abcdef,16,8,2,1,0x888,0xfffe,8,384,2,True,True,0x0
        1032456789abcdef,16,8,2,1,0x2aaa,0xfffe,192,3072,4,True,True,0x0

    """
    smart_print = get_smart_print(filename)

    smart_print("lut," + properties.get_property_names())

    n = get_bitsize(candidates[0])
    num_char_per_elem = len(hex(n - 1)) - 2

    def lut2hex(lut):
        return lut2hex_string(lut, num_char_per_elem=num_char_per_elem, prefix0x=False)

    if add_identity_row:
        smart_print(f"{lut2hex(list(range(2**n)))},{properties.get_properties_identity()}")
    if add_inversion_row:
        smart_print(f"{lut2hex(get_lut_inversion(n))},{properties.get_properties_inversion()}")

    for i, lut in enumerate(candidates):
        if not isinstance(lut, list):
            lut = list(lut)
        lut_properties = properties.get_properties(lut, verbose=verbose, filename=filename, **sat_args)
        smart_print(f"{lut2hex(lut)},{lut_properties}")
