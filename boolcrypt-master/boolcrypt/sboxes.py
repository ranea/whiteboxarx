"""List of S-boxes with bitsize between 3 and 6."""
import pathlib

from boolcrypt.utilities import hex_string2lut


# -------------
# 3-bit S-Boxes
# -------------

linear_3b_classes = [
    (0, 1, 2, 3, 4, 5, 6, 7),
    (0, 1, 2, 3, 4, 5, 7, 6),
    (0, 1, 2, 3, 4, 6, 7, 5),
    (0, 1, 2, 4, 3, 6, 7, 5),
    (1, 0, 2, 3, 4, 5, 6, 7),
    (1, 0, 2, 3, 4, 5, 7, 6),
    (1, 0, 2, 3, 4, 6, 5, 7),
    (1, 0, 2, 3, 4, 6, 7, 5),
    (1, 0, 2, 4, 3, 6, 5, 7),
    (1, 0, 2, 4, 3, 6, 7, 5)
]

affine_3b_classes = [
    (0, 1, 2, 3, 4, 5, 6, 7),
    (0, 1, 2, 3, 4, 5, 7, 6),
    (0, 1, 2, 3, 4, 6, 7, 5),
    (0, 1, 2, 4, 3, 6, 7, 5),  # inversion
]


# -------------
# 4-bit S-Boxes
# -------------


# high_sym means more (or equal) self-equivalences than inversion
high_se_4bit_sboxes = [
    "801CF56743AB9DE2",
    "6512304789ABCDEF",
    "10432567F9ABCDE8",
    "20135467A98BCDEF",
    "2013746589ABCDEF",
    "1043256789ABCDEF",
    "2013456789ABCDEF",
    "80A23517496BCDEF",
    "40132567C89BADEF",
    "40623517A98BCDEF",
    "4062351789ABCDEF",
    "2013645789ABCDEF",
    "3012654789ABCDEF",
    "3012456789ABCDEF",
    "1023456789ABCDEF",
    "1032456789ABCDEF",
    "0123456789ABCDEF"
]
high_se_4bit_sboxes = [hex_string2lut(l, 1) for l in high_se_4bit_sboxes]


high_se_4bit_2deg_sboxes = [
    "6512304789ABCDEF",
    "40132567C89BADEF",
    "40623517A98BCDEF",
    "2013645789ABCDEF",
    "3012654789ABCDEF",
    "1032456789ABCDEF"
]
high_se_4bit_2deg_sboxes = [hex_string2lut(l, 1) for l in high_se_4bit_2deg_sboxes]


def get_4bit_permutations():
    classes = []
    try:
        path_sboxes = pathlib.Path(__file__).parent / "sboxes/4bit-AffineClasses.txt"
    except NameError:
        path_sboxes = "boolcrypt/sboxes/4bit-AffineClasses.txt"
    with open(path_sboxes) as file:
        for line in file:
            classes.append(hex_string2lut(line.rstrip(), 1))
    return classes


def get_4bit_2d_permutations():
    from boolcrypt.utilities import get_algebraic_degree
    classes = []
    try:
        path_sboxes = pathlib.Path(__file__).parent / "sboxes/4bit-AffineClasses.txt"
    except NameError:
        path_sboxes = "boolcrypt/sboxes/4bit-AffineClasses.txt"
    with open(path_sboxes) as file:
        for line in file:
            lut = hex_string2lut(line.rstrip(), 1)
            # print(line, get_algebraic_degree(lut))
            if get_algebraic_degree(lut) == 2:
                classes.append(lut)
    return classes


# -------------
# 5-bit S-Boxes
# -------------


# inv2deg means the inverse is also a quadratic permutation
inv2deg_5bit_2deg_sboxes = [
    "000102030405060708090a0b0c0d0e0f101112131415161719181b1a1d1c1f1e",
    "000102030405060708090a0b0c0d0e0f10111213151417161a1b18191f1e1d1c",
    "000102030405060708090a0b0c0d0e0f10111213151417161c1d1e1f19181b1a",
    "000102030405060708090a0b0c0d0e0f1011121318191a1b1c1d1e1f14151617",
    "000102030405060708090a0b0c0d0e0f10111312161715141c1d1f1e1a1b1918",
    "000102030405060708090a0b0c0d0e0f1011131218191b1a1c1d1f1e14151716",
    "000102030405060708090a0b0c0d0e0f1011141518191c1d161712131e1f1a1b",
    "000102030405060708090a0b0c0d0e0f10121311181a1b191c1e1f1d14161715",
    "000102030405060708090a0b0c0d0e0f10121311181a1b191d1f1e1c15171614",
    "000102030405060708090a0b0c0d0e0f10121416181a1c1e131117151b191f1d",
    "000102030405060708090a0b0c0d0e0f10121416181a1c1e1f1d1b1917151311",
    "000102030405060708090a0b0d0c0f0e10111213161714151c1d1e1f1b1a1918",
    "000102030405060708090a0b0d0c0f0e1011121318191a1b1c1d1e1f15141716",
    "000102030405060708090a0b0d0c0f0e101113121415171618191b1a1d1c1e1f",
    "000102030405060708090a0b0d0c0f0e10111312141517161a1b19181f1e1c1d",
    "000102030405060708090a0b0d0c0f0e10111312161715141c1d1f1e1b1a1819",
    "000102030405060708090a0b0d0c0f0e1011131218191b1a1c1d1f1e15141617",
    "000102030405060708090a0b101112130c0d0e0f18191a1b1c1d1e1f14151617",
]
inv2deg_5bit_2deg_sboxes = [hex_string2lut(l, 2) for l in inv2deg_5bit_2deg_sboxes]


inv3deg_5bit_2deg_sboxes = [
    "000102030405060708090a0b0d0c0f0e101114151213161718191c1d1b1a1f1e",
    "000102030405060708090a0b0d0c0f0e10111415121316171a1b1e1f19181d1c",
    "000102030405060708090a0b0d0c0f0e101114151617121318191c1d1f1e1b1a",
    "000102030405060708090a0b0d0c0f0e1011141518191c1d121316171b1a1f1e",
    "000102030405060708090a0b0d0c0f0e1011141518191c1d161712131f1e1b1a",
    "000102030405060708090a0b0d0c0f0e1011141518191c1d1e1f1a1b17161312",
    "000102030405060708090a0b0d0c0f0e10121113181a191b1c1e1d1f15171416",
    "000102030405060708090a0b0d0c0f0e1012131114161715181a1b191d1f1e1c",
    "000102030405060708090a0b0d0c0f0e10121311141617151c1e1f1d191b1a18",
    "000102030405060708090a0b0d0c0f0e10121311181a1b191c1e1f1d15171614",
    "000102030405060708090a0b0d0c0f0e1014111512161317181c191d1b1f1a1e",
    "000102030405060708090a0b0d0c0f0e10141115181c191d121613171b1f1a1e",
    "000102030405060708090a0b101112130c0d0f0e161715141c1d1f1e1a1b1918",
    "000102030405060708090a0b101112130c0d0f0e18191b1a1c1d1f1e14151716",
    "000102030405060708090a0b101112130c0e0f0d14161715181a1b191c1e1f1d",
    "000102030405060708090a0b101112130c0e0f0d141617151c1e1f1d181a1b19",
    "000102030405060708090a0b101112130c0e0f0d181a1b191c1e1f1d14161715",
    "000102030405060708090a0b101112130c0e0f0d181a1b191d1f1e1c15171614",
    "000102030405060708090b0a0e0f0d0c1012141611131517181a1d1f1b191e1c",
    "000102030405060708090b0a0e0f0d0c1012141613111715181a1d1f191b1c1e",
    "000102030405060708090b0a0e0f0d0c1012161413111517181a1f1d191b1e1c",
    "000102030405060708090b0a0e0f0d0c1012181a1113191b14161d1f17151e1c",
    "000102030405060708090b0a0e0f0d0c1014121613171115181c1b1f191d1a1e",
    "000102030405060708090b0a0e0f0d0c1014161217131115181c1f1b1d191a1e",
    "000102030405060708090b0a0e0f0d0c1018121a131b1119141c171f151d161e",
    "000102030405060708090c0d0e0f0a0b1018121a1c141e161119151d1f171b13",
    "0001020304050607080a0c0e0b090f0d1014131716121511181f1d1a191e1c1b",
    "000102030405070608090c0d0e0f0b0a1012181a14161d1f15171b1913111c1e",
    "000102030405070608090c0d0e0f0b0a1012181a16141f1d15171b1911131e1c",
    "000102030405070608090c0d0e0f0b0a1012181a16141f1d1715191b13111c1e",
    "000102030405070608090c0d0e0f0b0a10121a1816141d1f1517191b11131c1e",
    "000102030405070608090c0d0e0f0b0a1018121a141c171f151d1119131b161e",
    "000102030405070608090c0d0e0f0b0a10181a121c14171f151d19111b13161e",
    "000102030405070608090c0d0e0f0b0a10181a121c14171f1d151119131b1e16",
    "0001020304050706080a0c0e10121517090d0b0f181c1b1f191e1d1a14131116",
    "000102030405070608100a120c140f1709180b1a0d1c0e1f19111b131d151e16",
    "000102030405070608100a120c140f1709180b1a0e1f0d1c19111b131e161d15",
    "000102030405070608100a120c140f1709180d1c0e1f0b1a1119151d161e131b",
    "000102030405070608100a120c140f1709180d1c0e1f0b1a19111d151e161b13",
    "000102030405070608100a120c140f17091a0d1e0b180e1d111b151f1319161c",
    "000102030405070608100a120c140f17091a0d1e0e1d0b18111b151f161c1319",
    "000102030405080906070c0d0e0f0a0b1013111214171b1815161c1f1d1e1a19",
    "0001020304050809060a0b07101c131f0c0e0f0d1416191b121d1e1118171a15",
    "0001020304050809060a0b07101c131f0c0e0f0d1416191b1d12111e1718151a",
    "0001020304050809060a0b07101c131f0c0e0f0d1517181a121d1e1119161b14",
    "0001020304050809060a0b07101c131f0c0e0f0d1517181a1d12111e1619141b",
    "0001020304050809060a101c070b1f130c0e14160d0f1b19111e1d12151a1718",
    "0001020304050809060a101c070b1f130c0e14160f0d191b111e1d121718151a",
    "0001020304050809060a101c070b1f130c0e15170f0d181a141b1916121d111e",
    "000102030405080906100a1c0d1b0f1907140c1f0b180e1d1216171311151a1e",
    "000102030405080906100a1c0d1b0f19071f0c140e160b131718121d111e1a15",
    "000102030405080906100a1c0f190d1b07140e1d0c1f0b181511121613171a1e",
    "000102030406080a050c1019070d1c16090f11170b0e1d181a14151b1e131f12",
    "000102030406080a050c1019070d1c16090f181e0b0e14111b151d131f12171a",
    "000102030406080a050c10190d07161c090e13140f0b1b1f1817151a121e111d",
    "000102040308101c050a191112171f1d06140d18130b09161b070e151a0c1e0f",
    "000102040308101c050a1a1211141f1d0615180c160f19070e130d17091e1b0b",
]
inv3deg_5bit_2deg_sboxes = [hex_string2lut(l, 2) for l in inv3deg_5bit_2deg_sboxes]


# -------------
# 6-bit S-Boxes
# -------------


def get_quadratic_6bit_permutations():
    classes = []
    try:
        path_sboxes = pathlib.Path(__file__).parent / "sboxes/2deg-6bit-AffineClasses.txt"
    except NameError:
        path_sboxes = "boolcrypt/sboxes/2deg-6bit-AffineClasses.txt"
    with open(path_sboxes) as file:
        for line in file:
            # lut = [int(character) for character in line.split()]
            lut = hex_string2lut(line.rstrip(), 2)
            classes.append(lut)
    return classes


# source: Results on rotation-symmetric S-boxes
rssb_6bit = [
    "000a1438281f3103111b3e1723010639223736103d152e34073a02090c133319" +
    "051c2f212d2b203c3b082a1a1d24292c0e30351e040d1216180f260b2725323f",
    "0013260e0d3b1c271a09372238010f03343e12102f15052c311402361e320635" +
    "29073d33241120211f082a160a1b193a23392830040b2d1d3c18252e0c172b3f",
    "000a1404281f0833111b3e32103427232237360d3d152517201629090f1d0718" +
    "05022f392d191a313b262a2b0b242e0c013c2c38133512061e1c3a030e21303f",
    "000306070c2b0e39180917321c0d333b303a12132e15251038161a3627013714" +
    "2123353c2419263d1d292a080b1b200a311e2c3e34042d050f1f02222f11283f",
]
rssb_6bit = [hex_string2lut(l, 2) for l in rssb_6bit]