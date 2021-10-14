pallas_q = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
vesta_q = 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001
pallas_f = GF(pallas_q)
vesta_f = GF(vesta_q)
#print(factor(pallas_p-1))
#print(factor(vesta_p-1))

from collections import namedtuple

class EcAffPt(namedtuple('EcPt', ['x', 'y', 'inf'])):
    pass

class WeiestrassEc(namedtuple('WeiestrassEc', ['a', 'b', 'q'])):
    def to_mg(self):

        return MontgomeryEc(
                A = Vk


class MontgomeryEc(namedtuple('MontgomeryEc', ['A', 'B', 'q'])):
    def to_sw(self):
        return WeiestrassEc(
                a = (3 - mg.A ** 2) / (3 * mg.B ** 2),
                b = (2 * mg.A ** 3 - 9 * mg.A) / (27 * mg.B ** 3),
                q = mg.q)

    def to_te(self):
        return TwistedEdwardsEc(
                a = (mg.A + 2) / mg.B,
                d = (mg.A - 2) / mg.B,
                q = mg.q)




class TwistedEdwardsEc(namedtuple('TwistedEdwardsEc', ['a', 'd', 'q'])):
    pass


pallas_sw = WeiestrassEc(pallas_f.zero() + 1, pallas_f.zero() + 5, pallas_p)
vesta_sw = WeiestrassEc(vesta_f.zero() + 1, vesta_f.zero() + 5, vesta_p)

print(pallas_sw)
print(vesta_sw)
