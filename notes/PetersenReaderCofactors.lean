import Mathlib
namespace PetersenReaderGrammar
abbrev Label := Fin 63
abbrev High := BitVec 3
abbrev Rule := Bool × Label × Label × Label
def waves : Array (Array Nat) := #[#[0x0,0x7fffffffffffffff,0x0,0x0,0x0,0x0,0x0,0x1],#[0x7fffffffffffffff,0x0,0x18000001,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x18000001,0x18000003],#[0x7fffffffffffffff,0x0,0x780003f7,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x780003f7,0x780003f7],#[0x7fffffffffffffff,0x0,0x0,0x0,0x0,0x0,0x0,0x7fffffffffffffff],#[0x7fffffffffffffff,0x0,0x60,0x0,0x120000000000800,0x0,0x0,0x10],#[0x7fffffffffffffff,0x0,0x40,0x0,0x7fffffffffffffff,0x40,0x40,0x60],#[0x0,0x0,0x0,0x0,0x7fffffffffffffff,0x0,0x0,0x40],#[0x0,0x0,0x0,0x0,0x0,0x7fffffffffffffff,0x0,0xc1],#[0x7fffffffffffffff,0x0,0x780003f7,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x780003f7,0x780003f7],#[0x0,0x0,0x0,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x780003f7,0x780003f7],#[0x7fffffffffffffff,0x0,0x780003f7,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x780003f7,0x7fffffffffffffff],#[0x0,0x0,0x7fffffffffffffff,0x0,0x0,0x0,0x0,0x800],#[0x0,0x0,0x7fffffffffffffff,0x0,0x0,0x0,0x0,0x7fffffffffffffff],#[0x7fffffffffffffff,0xc000,0x0,0x0,0x60000000000001,0x0,0x0,0x2000],#[0x7fffffffffffffff,0x8000,0x0,0x0,0x7c60018080006001,0x0,0x0,0x4000],#[0x0,0x0,0x0,0x0,0x7fffffffffffffff,0x0,0x0,0x8000],#[0x7fffffffffffffff,0xc000,0x18000001,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x18000001,0x18012003],#[0x7fffffffffffffff,0xc000,0x18000001,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x18000001,0x18036003],#[0x7fffffffffffffff,0xc000,0x780003f7,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x780003f7,0x780523f7],#[0x7fffffffffffffff,0xc000,0x780003f7,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x780003f7,0x780f63f7],#[0x7fffffffffffffff,0xc000,0x60,0x0,0x160000000000801,0x0,0x0,0x102010],#[0x7fffffffffffffff,0xc000,0x60,0x0,0x7fffffffffffffff,0xc040,0x60,0x302070],#[0x7fffffffffffffff,0xc000,0x60,0x0,0x7d60018080006801,0x4000,0x0,0x506010],#[0x7fffffffffffffff,0xc000,0x60,0x0,0x7fffffffffffffff,0xc040,0x60,0xf06070],#[0x7fffffffffffffff,0xc000,0x780003f7,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x780003f7,0x793523f7],#[0x7fffffffffffffff,0xc000,0x780003f7,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x780003f7,0x7bff63f7],#[0x0,0x0,0x0,0x0,0x0,0x0,0x7fffffffffffffff,0x4008800],#[0x0,0x0,0x0,0x0,0x7fffffffffffffff,0x0,0x0,0x8000000],#[0x0,0x0,0x0,0x0,0x0,0x7fffffffffffffff,0x0,0x18000001],#[0x0,0x0,0x0,0x0,0x7fffffffffffffff,0x0,0x0,0x28000040],#[0x0,0x0,0x0,0x0,0x0,0x7fffffffffffffff,0x0,0x780003f7],#[0x7fffffffffffffff,0x0,0x0,0x0,0x400000000000000,0x0,0x400008000000000,0x80000000],#[0x0,0x0,0x0,0x0,0x0,0x0,0x7fffffffffffffff,0x108000800],#[0x7fffffffffffffff,0x0,0x18000001,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x400008018000001,0x400008298000003],#[0x7fffffffffffffff,0x0,0x780003f7,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x4000080780003f7,0x4000086f80003f7],#[0x7fffffffffffffff,0x0,0x60,0x0,0x520000000000800,0x0,0x400008000000000,0x880000010],#[0x7fffffffffffffff,0x0,0x60,0x0,0x7fffffffffffffff,0x40,0x400008000000060,0x1880000070],#[0x7fffffffffffffff,0x0,0x780003f7,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x4000080780003f7,0x40000bef80003f7],#[0x0,0x0,0x0,0x0,0x7fffffffffffffff,0x0,0x0,0x4008008000],#[0x7fffffffffffffff,0x0,0x0,0x0,0x400000000000000,0x0,0x400000000000000,0x8000000000],#[0x7fffffffffffffff,0x3808000e000,0x0,0x0,0x7c60018080006001,0x18080006000,0x1400018080006000,0x18080006000],#[0x0,0x0,0x0,0x0,0x7fffffffffffffff,0x3808000e000,0x1400018080006000,0x3808000e000],#[0x0,0x0,0x0,0x0,0x0,0x0,0x7fffffffffffffff,0x7c18c00e800],#[0x7fffffffffffffff,0x0,0x18000001,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x400008018000001,0x400088298000003],#[0x7fffffffffffffff,0x3808000e000,0x18000001,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x1400018098006001,0x1400198298036003],#[0x7fffffffffffffff,0x0,0x780003f7,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x4000080780003f7,0x4002886f80003f7],#[0x7fffffffffffffff,0x3808000e000,0x780003f7,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x14000180f80063f7,0x14007986f80f63f7],#[0x7fffffffffffffff,0x0,0x60,0x0,0x520000000000800,0x0,0x400008000000000,0x808880000010],#[0x7fffffffffffffff,0x3808000e000,0x60,0x0,0x7d60018080006801,0x18080006000,0x1400018080006000,0x1818880506010],#[0x7fffffffffffffff,0x0,0x60,0x0,0x7fffffffffffffff,0x40,0x400008000000060,0x2809880000070],#[0x7fffffffffffffff,0x3808000e000,0x60,0x0,0x7fffffffffffffff,0x3808000e040,0x1400018080006060,0x7819880f06070],#[0x7fffffffffffffff,0x0,0x780003f7,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x4000080780003f7,0x40aa8bef80003f7],#[0x7fffffffffffffff,0x3808000e000,0x780003f7,0x0,0x7fffffffffffffff,0x7fffffffffffffff,0x14000180f80063f7,0x141ff9befbff63f7],#[0x7fffffffffffffff,0x0,0x0,0x0,0x0,0x0,0x0,0x20000000000000],#[0x0,0x7fffffffffffffff,0x0,0x0,0x0,0x0,0x0,0x60000000000001],#[0x7fffffffffffffff,0x0,0x0,0x0,0x0,0x0,0x0,0x7fffffffffffffff],#[0x0,0x0,0x7fffffffffffffff,0x0,0x0,0x0,0x0,0x120000000000800],#[0x0,0x0,0x7fffffffffffffff,0x0,0x0,0x0,0x7fffffffffffffff,0x7fffffffffffffff],#[0x7fffffffffffffff,0x0,0x0,0x0,0x0,0x0,0x0,0x400000000000000],#[0x0,0x7fffffffffffffff,0x0,0x0,0x0,0x0,0x0,0xc00000000000001],#[0x7fffffffffffffff,0x3808000e000,0x0,0x0,0x7c60018080006001,0x18080006000,0x1400018080006000,0x1400018080006000],#[0x7fffffffffffffff,0x0,0x0,0x0,0x0,0x0,0x0,0x2420000000000000],#[0x0,0x7fffffffffffffff,0x0,0x0,0x0,0x7c60018080006001,0x0,0x7c60018080006001]]
def labels : Array (BitVec 256) := #[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888,0xccccccccc8c8c8c8ccccccccc8c8c8c8ccccccccc8c8c8c8ccccccccc8c8c8c8,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f000,0xf0f0f0f0f0f0f0f0f0c0f0c0f0c0f0c0f0f0f0f0f0f0f0f0f0c0f0c0f0c0f0c0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,0xfcfcfcfcf8f8f8f8fcccfcccf8c8f8c8fcfcfcfcf8f8f8f8fcccfcccf8c8f8c8,0xfcfcfcfcf8f8f8f8fcfcfcfcf8f8f8f8fcfcfcfcf8f8f8f8fcfcfcfcf8f8f8f8,0xfcfcfcfcfcfcfcfcfcccfcccfcccfcccfcfcfcfcfcfcfcfcfcccfcccfcccfccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,0xffff0000ffff0000aaaa0000aaaa0000ffff0000ffff0000aaaa0000aaaa0000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffccccffff8888eeeeccccaaaa8888ffffccccffff8888eeeeccccaaaa8888,0xffffccccffff8888ffffccccffff8888ffffccccffff8888eeeeccccaaaa8888,0xffffccccffffc8c8eeeecccceaeac8c8ffffccccffffc8c8eeeecccceaeac8c8,0xffffccccffffc8c8ffffccccffffc8c8ffffccccffffc8c8eeeecccceaeac8c8,0xfffff0f0fffff0f0faaaf000faaaf000fffff0f0fffff0f0faaaf000faaaf000,0xfffff0f0fffff0f0faeaf0c0faeaf0c0fffff0f0fffff0f0faeaf0c0faeaf0c0,0xfffff0f0fffff0f0fffff000fffff000fffff0f0fffff0f0faaaf000faaaf000,0xfffff0f0fffff0f0fffff0c0fffff0c0fffff0f0fffff0f0faeaf0c0faeaf0c0,0xfffffcfcfffff8f8feeefcccfaeaf8c8fffffcfcfffff8f8feeefcccfaeaf8c8,0xfffffcfcfffff8f8fffffcccfffff8c8fffffcfcfffff8f8feeefcccfaeaf8c8,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafa,0xffffffffff00ff00ffffffffff00ff0000000000000000000000000000000000,0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,0xffffffffff88ff88ffffffffff88ff88cccccccc88888888cccccccc88888888,0xffffffffffc8ffc8ffffffffffc8ffc8ccccccccc8c8c8c8ccccccccc8c8c8c8,0xfffffffffff0fff0ffffffffff00ff00f0f0f0f0f0f0f0f0f000f000f000f000,0xfffffffffff0fff0ffffffffffc0ffc0f0f0f0f0f0f0f0f0f0c0f0c0f0c0f0c0,0xfffffffffff8fff8ffffffffffc8ffc8fcfcfcfcf8f8f8f8fcccfcccf8c8f8c8,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,0xffffffffffffff00ffffffffffffff0000000000000000000000000000000000,0xffffffffffffff00ffffffffffffff00ffff0000ffff0000aaaa0000aaaa0000,0xffffffffffffff00ffffffffffffff00ffff0000ffff0000ffff0000ffff0000,0xffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00,0xffffffffffffff88ffffffffffffff88cccccccc88888888cccccccc88888888,0xffffffffffffff88ffffffffffffff88ffffccccffff8888eeeeccccaaaa8888,0xffffffffffffffc8ffffffffffffffc8ccccccccc8c8c8c8ccccccccc8c8c8c8,0xffffffffffffffc8ffffffffffffffc8ffffccccffffc8c8eeeecccceaeac8c8,0xfffffffffffffff0ffffffffffffff00f0f0f0f0f0f0f0f0f000f000f000f000,0xfffffffffffffff0ffffffffffffff00fffff0f0fffff0f0faaaf000faaaf000,0xfffffffffffffff0ffffffffffffffc0f0f0f0f0f0f0f0f0f0c0f0c0f0c0f0c0,0xfffffffffffffff0ffffffffffffffc0fffff0f0fffff0f0faeaf0c0faeaf0c0,0xfffffffffffffff8ffffffffffffffc8fcfcfcfcf8f8f8f8fcccfcccf8c8f8c8,0xfffffffffffffff8ffffffffffffffc8fffffcfcfffff8f8feeefcccfaeaf8c8,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00,0xffffffffffffffffffccffccffccffccffffffffffffffffffccffccffccffcc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffffffff0000ffff0000aaaa0000aaaa0000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa]
def base : Fin 8 → Label := ![0,3,6,11,15,27,53,58]
def baseHigh : Fin 8 → High := ![1,0,4,2,4,4,0,0]
def goal : Label := 52
def rules : List Rule := [(true,0,6,7),(true,0,27,28),(true,0,29,30),(true,0,53,54),(true,0,58,59),(true,0,61,62),(true,1,5,8),(true,1,6,9),(true,1,13,16),(true,1,14,17),(true,1,21,24),(true,1,23,25),(true,1,31,33),(true,1,36,37),(true,1,39,43),(true,1,40,44),(true,1,49,51),(true,1,50,52),(true,2,4,8),(true,2,5,8),(true,2,6,9),(true,2,13,18),(true,2,14,19),(true,2,16,18),(true,2,17,19),(true,2,20,24),(true,2,21,24),(true,2,22,25),(true,2,23,25),(false,2,28,1),(true,2,31,34),(true,2,33,34),(true,2,35,37),(true,2,36,37),(true,2,39,45),(true,2,40,46),(true,2,43,45),(true,2,44,46),(true,2,47,51),(true,2,48,52),(true,2,49,51),(true,2,50,52),(true,3,4,10),(true,3,5,10),(false,3,8,2),(true,3,8,10),(false,3,9,2),(true,3,11,12),(false,3,28,1),(false,3,30,2),(true,3,53,55),(true,3,56,57),(true,4,13,20),(true,4,14,22),(true,4,18,24),(true,4,19,25),(true,4,31,35),(true,4,34,37),(true,4,39,47),(true,4,40,48),(true,4,45,51),(true,4,46,52),(true,5,13,21),(true,5,14,23),(true,5,16,24),(true,5,17,25),(true,5,18,24),(true,5,19,25),(true,5,20,21),(true,5,22,23),(true,5,31,36),(true,5,33,37),(true,5,34,37),(true,5,35,36),(true,5,39,49),(true,5,40,50),(true,5,43,51),(true,5,44,52),(true,5,45,51),(true,5,46,52),(true,5,47,49),(true,5,48,50),(false,5,56,4),(false,6,8,5),(true,6,8,9),(false,6,10,5),(true,6,27,29),(true,6,28,30),(false,6,56,4),(false,6,57,5),(true,7,27,30),(true,7,28,30),(true,7,29,30),(true,8,13,24),(true,8,14,25),(true,8,16,24),(true,8,17,25),(true,8,18,24),(true,8,19,25),(true,8,20,24),(true,8,21,24),(true,8,22,25),(true,8,23,25),(true,8,31,37),(true,8,33,37),(true,8,34,37),(true,8,35,37),(true,8,36,37),(true,8,39,51),(true,8,40,52),(true,8,43,51),(true,8,44,52),(true,8,45,51),(true,8,46,52),(true,8,47,51),(true,8,48,52),(true,8,49,51),(true,8,50,52),(false,9,10,8),(true,9,28,30),(false,9,57,8),(false,10,30,8),(true,10,56,57),(true,11,15,26),(true,11,27,32),(true,11,38,42),(true,11,53,56),(true,11,55,57),(true,12,53,57),(true,12,55,57),(true,12,56,57),(true,13,39,40),(true,13,43,44),(true,13,45,46),(true,13,47,48),(true,13,49,50),(true,13,51,52),(true,13,58,60),(true,14,16,17),(true,14,18,19),(true,14,20,22),(true,14,21,23),(true,14,24,25),(true,14,31,40),(true,14,33,44),(true,14,34,46),(true,14,35,48),(true,14,36,50),(true,14,37,52),(true,14,39,40),(true,14,43,44),(true,14,45,46),(true,14,47,48),(true,14,49,50),(true,14,51,52),(false,14,54,13),(true,14,58,60),(true,15,27,38),(true,15,31,41),(true,15,32,42),(true,15,39,41),(false,15,40,14),(true,15,40,41),(false,15,54,13),(false,15,60,14),(false,15,62,14),(true,16,21,24),(true,16,23,25),(true,16,39,44),(true,16,40,44),(true,16,43,44),(true,16,45,46),(true,16,49,52),(true,16,50,52),(true,16,51,52),(true,17,18,19),(true,17,21,25),(true,17,23,25),(true,17,24,25),(true,17,31,44),(true,17,33,44),(true,17,34,46),(true,17,36,52),(true,17,37,52),(true,17,39,44),(true,17,40,44),(true,17,43,44),(true,17,45,46),(true,17,49,52),(true,17,50,52),(true,17,51,52),(true,18,20,24),(true,18,21,24),(true,18,22,25),(true,18,23,25),(true,18,39,46),(true,18,40,46),(true,18,43,46),(true,18,44,46),(true,18,45,46),(true,18,47,52),(true,18,48,52),(true,18,49,52),(true,18,50,52),(true,18,51,52),(true,19,20,25),(true,19,21,25),(true,19,22,25),(true,19,23,25),(true,19,24,25),(true,19,31,46),(true,19,33,46),(true,19,34,46),(true,19,35,52),(true,19,36,52),(true,19,37,52),(true,19,39,46),(true,19,40,46),(true,19,43,46),(true,19,44,46),(true,19,45,46),(true,19,47,52),(true,19,48,52),(true,19,49,52),(true,19,50,52),(true,19,51,52),(true,20,39,48),(true,20,40,48),(true,20,45,52),(true,20,46,52),(true,20,47,48),(true,20,49,50),(true,20,51,52),(true,21,22,23),(true,21,39,50),(true,21,40,50),(true,21,43,52),(true,21,44,52),(true,21,45,52),(true,21,46,52),(true,21,47,50),(true,21,48,50),(true,21,49,50),(true,21,51,52),(true,22,24,25),(true,22,31,48),(true,22,34,52),(true,22,35,48),(true,22,36,50),(true,22,37,52),(true,22,39,48),(true,22,40,48),(true,22,45,52),(true,22,46,52),(true,22,47,48),(true,22,49,50),(true,22,51,52),(true,23,24,25),(true,23,31,50),(true,23,33,52),(true,23,34,52),(true,23,35,50),(true,23,36,50),(true,23,37,52),(true,23,39,50),(true,23,40,50),(true,23,43,52),(true,23,44,52),(true,23,45,52),(true,23,46,52),(true,23,47,50),(true,23,48,50),(true,23,49,50),(true,23,51,52),(true,24,39,52),(true,24,40,52),(true,24,43,52),(true,24,44,52),(true,24,45,52),(true,24,46,52),(true,24,47,52),(true,24,48,52),(true,24,49,52),(true,24,50,52),(true,24,51,52),(true,25,31,52),(true,25,33,52),(true,25,34,52),(true,25,35,52),(true,25,36,52),(true,25,37,52),(true,25,39,52),(true,25,40,52),(true,25,43,52),(true,25,44,52),(true,25,45,52),(true,25,46,52),(true,25,47,52),(true,25,48,52),(true,25,49,52),(true,25,50,52),(true,25,51,52),(true,26,27,42),(true,26,32,42),(true,26,38,42),(true,28,29,30),(true,32,38,42),(false,32,39,31),(true,32,41,42),(false,32,58,31),(true,33,36,37),(true,33,39,43),(true,33,40,44),(true,33,49,51),(true,33,50,52),(true,34,35,37),(true,34,36,37),(true,34,39,45),(true,34,40,46),(true,34,43,45),(true,34,44,46),(true,34,47,51),(true,34,48,52),(true,34,49,51),(true,34,50,52),(true,35,39,47),(true,35,40,48),(true,35,45,51),(true,35,46,52),(true,36,39,49),(true,36,40,50),(true,36,43,51),(true,36,44,52),(true,36,45,51),(true,36,46,52),(true,36,47,49),(true,36,48,50),(true,37,39,51),(true,37,40,52),(true,37,43,51),(true,37,44,52),(true,37,45,51),(true,37,46,52),(true,37,47,51),(true,37,48,52),(true,37,49,51),(true,37,50,52),(true,40,43,44),(true,40,45,46),(true,40,47,48),(true,40,49,50),(true,40,51,52),(false,40,58,39),(true,40,58,60),(false,41,58,39),(false,41,60,40),(false,41,62,40),(false,42,58,39),(false,42,60,40),(true,43,49,51),(true,43,50,52),(true,44,45,46),(true,44,49,52),(true,44,50,52),(true,44,51,52),(true,45,47,51),(true,45,48,52),(true,45,49,51),(true,45,50,52),(true,46,47,52),(true,46,48,52),(true,46,49,52),(true,46,50,52),(true,46,51,52),(true,48,49,50),(true,48,51,52),(true,50,51,52),(true,53,58,61),(true,53,59,62),(true,54,58,62),(true,54,59,62),(true,54,60,62),(true,54,61,62),(true,55,56,57),(true,59,61,62)]

def masks (u : Label) (y : High) := ((waves[u.val]?).getD #[])[y.toNat]?.getD 0
def combine (op : Bool) (a b : High) := if op then a ||| b else a &&& b
def ruleClosed (r : Rule) := (List.finRange 8).all fun i => (List.finRange 8).all fun j =>
  let a := BitVec.ofFin i
  let b := BitVec.ofFin j
  let ab := masks r.2.1 a &&& masks r.2.2.1 b
  ab &&& masks r.2.2.2 (combine r.1 a b) == ab

theorem pass : rules.all ruleClosed = true := by decide +kernel
theorem permittedBase : ∀ i : Fin 8, ∀ p : Label, (masks (base i) (baseHigh i)).testBit p.val = true := by decide +kernel
theorem permittedFirst : ∀ p : Label, (masks (base 1) 7).testBit p.val = true := by decide +kernel
theorem permittedPin : ∀ p : Label, (masks p 7).testBit p.val = true := by decide +kernel
theorem miss : masks goal 3 = 0 := by decide +kernel

inductive Realizes (p : Label) : Label → High → Prop where
  | atom (i : Fin 8) : Realizes p (base i) (baseHigh i)
  | first : Realizes p (base 1) 7
  | special : Realizes p p 7
  | gate {op a b c i j} : (op,a,b,c) ∈ rules → Realizes p a i → Realizes p b j →
      Realizes p c (combine op i j)
  | swapped {op a b c i j} : (op,b,a,c) ∈ rules → Realizes p a i → Realizes p b j →
      Realizes p c (combine op i j)

theorem closed {op a b c} (r : (op,a,b,c) ∈ rules) (i j : High) (p : Label)
    (x : (masks a i).testBit p.val=true) (y : (masks b j).testBit p.val=true) :
    (masks c (combine op i j)).testBit p.val=true := by
  have check := List.all_eq_true.mp pass _ r
  have ci := List.all_eq_true.mp check i.toFin (by simp)
  have cij := List.all_eq_true.mp ci j.toFin (by simp)
  change (masks a i &&& masks b j &&& masks c (combine op i j) == masks a i &&& masks b j) = true at cij
  have eq := congrArg (fun n : Nat => n.testBit p.val) (beq_iff_eq.mp cij)
  simpa only [Nat.testBit_and,x,y,Bool.true_and] using eq

theorem impossible (p : Label) : ¬Realizes p goal 3 := by
  have invariant {u y} (h : Realizes p u y) : (masks u y).testBit p.val=true := by
    induction h with
    | atom i => exact permittedBase i p
    | first => exact permittedFirst p
    | special => exact permittedPin p
    | gate m _ _ x y => exact closed m _ _ _ x y
    | @swapped op a b c i j m _ _ x y =>
      have h := closed m _ _ _ y x
      cases op <;> simpa [combine,BitVec.and_comm,BitVec.or_comm] using h
  intro h
  have hit := invariant h
  have nope := (congrArg (fun n : Nat => n.testBit p.val) miss).symm.trans hit
  simp at nope

abbrev Low := BitVec 256
def word (x : Label) : Low := labels[x.val]?.getD 0
def encode (x : Low) : Label := Fin.ofNat 63 ((0x33000000004000000000300000c0000000000000000000000000000000000000002a000bc00000000000000000010000000000000310000000000000320000000000000000000000000000003c00000009400005400000000190000000000000003b90000000200002400000020002007c003700000084000000003800070000088000000000000000000003c023000900000000000000012000e8003400000001d00002b0000000000000000000000000000130c000a03d00058000000000000001b000000000000b80ec001e03500000000003e4694000000000360000002c05c00000000000261da0285000000000000000001800000009c016c00000001834002d000000000 >>> (6*(x.toNat%359))) &&& 63)
def binary (op : Bool) (a b : Low) := if op then a ||| b else a &&& b
def whichData : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x740000000000000000000000,0x0,0xb85800000000000,0x188006000,0x0,0x0,0x0,0x0,0x0,0x290000000000000000000000000,0x550014c0000,0x0,0x2c9600000,0x0,0x0,0x0,0x0,0x0,0xec00,0x0,0x78,0x79000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x9b,0x0,0x528014800000000000518000000000000000000000000000014200,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x998000000000000000000000000000000000,0x4d40000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x5800000000000000000000000,0x0,0x0,0x2c800b1802c400,0x0,0x5980165000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80001000000000000000000000000000,0x1400000200000000000c0000000000000000000000000000000,0x580014000000000000002410000000000000001c0c00000000000,0xf07000000d000000000060000000000000000,0x2813090000000000000000000000000000000000000442000,0x78000000000000000070361a0c80000180b8002c15000000000,0x522813898000012890000011888000010880001f,0x5e00000b40000158a80000000000000000000000,0x0,0xcc0000190000000000000000000000000,0x371b00000001a8d00000000000000000000000,0x1e8f0000000000763a0000000001c8000038000000000,0x0,0x249208e00230000000000000000001140044219088240000fc7c00,0x512813c9c4d26000004b250000000,0x2a0000000000000000000000000,0x2b9580000000000000,0x0,0x2e16cb400000000000000000000000000000000000000000000000,0x0,0x2f1740000000000000000000000000000000000000000000000000,0xd66a349a0006700000000000000006632990c66230980be00,0x3a9d0e672389c0de6e00000da6c,0x0,0x77000000000,0x0,0x0,0x3d0000000000000000000000000000000000000000000000000000,0xf600000000000000000000000000000000000000000000000,0x7d00000000000000000000000f800000000000000000000,0xfe003f0000000000000000000000000,0x0,0x0,0x10481002000000,0x0,0x2240000000000000440010e00430010a00420000000418000000,0x460011600450000000000000000000000000000000000000000000,0x258000000254009449a4922900023c000000000000047000008d,0x13800000000000002680099002600097,0x13a00000000000000000000000000000000000000000000000,0x28940000000000000027d3c00,0x0,0xa7002980000000000000,0xae56ab00000002ac00aa0000152a8,0x588016000002bc0000000000000000000000000000000000000000,0x176005d00000b95c0016eb6002d568005980000000000000b2,0x5f2f57800,0x30982c05f8000000000000000000000000,0x33196ca64b2000c76331400006230c0000000000000,0x0,0x365b0006bb59aad469801a40000000000000345a0cf673340000,0x1c2e06fb79ba006e36db400,0x0,0x39c00e672b90000000001c6e2000000000000000000000000000,0xe8,0x3a40000000000000000000000,0x79801e4f1783bddced7600000eb750000000,0x0,0x7dbe800f97c3ddec00003d400000000000007a0000000,0x40000ff003f9fafc,0x4040000000000000000000000000000000000000000,0x222008843e1d0d8642e140000426100083c1a0b04818020400,0x0,0x0,0x11c8dc6a33188bc5a2b14000022712,0x0,0x94ca24f269280001249180245219047e3c008e8000000000000000,0x96cb2572a,0x978000000004b80000000000000000000000000000000000000000,0x26000000000000,0x0,0x0,0x0,0x0,0x4c40000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x990000000000000000000000000000000000000000000000000000,0x4d00000,0x0,0x1389b8000136000000000000000000000000000,0x4ea7200,0x0,0x28943a15040000a04fc00009f4f400009e4ec0000,0x0,0x51a8a00000000000000000000000000000000000000000000000,0x148a38000000,0x0,0x2a14fa7536994b000029549000000000000000000000000000,0x0,0x0,0x56ab358abd5aab54a98000152a88000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xb0800000000000015f00578015d00570015b000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x168b38000000000000000,0x0,0xb5da80000005a40000000000000000000000000000000000000000,0x16c,0x0,0x5c2df6eb68000000000000000000000000,0x0,0x0,0x5d6e973b95c40000,0x0,0x0,0x0,0x0,0x177005d80000000000000000000000,0x0,0x0,0x0,0x0,0x5e00000000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xbd5e40000000000000000000000000000000000000000000000000,0x0,0x0,0x17ebedf2f600000000000000000000000000000,0x0,0x0,0x5fc0000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc00000000000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]

def which (op : Bool) (a b : Label) :=
  let j := op.toNat*63*63 + a.val*63+b.val
  ((whichData[j/24]?.getD 0) >>> (9*(j%24))) &&& 511
def allPairs := [false,true].all fun op => (List.finRange 63).all fun a =>
  (List.finRange 63).all fun b =>
  let w := binary op (word a) (word b)
  let c := encode w
  if a.val < b.val && w == word c && c != a && c != b then
    rules[which op a b]? == some (op,a,b,c)
  else true
theorem identityLabels : ∀ x : Label, encode (word x)=x := by decide +kernel
theorem pairTable : allPairs = true := by decide +kernel
theorem identityHigh (i : Fin 8) : baseHigh i = BitVec.ofNat 3
    ((if (1:Nat).testBit i then 1 else 0) + (if (8:Nat).testBit i then 2 else 0) +
      (if (52:Nat).testBit i then 4 else 0)) := by fin_cases i <;> decide +kernel
theorem ruleOf {op : Bool} {a b c : Label} (ord : a.val<b.val)
    (actual : binary op (word a) (word b) = word c) (ca : c≠a) (cb : c≠b) :
    (op,a,b,c) ∈ rules := by
  have co := List.all_eq_true.mp pairTable op (by cases op <;> simp)
  have cx := List.all_eq_true.mp co a (by simp)
  have cxy := List.all_eq_true.mp cx b (by simp)
  have yes : decide (a.val < b.val) = true := decide_eq_true ord
  simp only [actual,identityLabels,yes,beq_self_eq_true,Bool.true_and,bne_iff_ne.mpr ca,
    bne_iff_ne.mpr cb,ite_true] at cxy
  exact List.mem_of_getElem? (beq_iff_eq.mp cxy)

theorem liftedGate {p op a b c i j} (x : Realizes p a i) (y : Realizes p b j)
    (actual : binary op (word a) (word b) = word c) (ca : c≠a) (cb : c≠b) :
    Realizes p c (combine op i j) := by
  rcases lt_trichotomy a.val b.val with ab|e|ba
  · exact .gate (ruleOf ab actual ca cb) x y
  · have eq : a=b := Fin.ext e
    subst b
    have same : binary op (word a) (word a) = word a := by cases op <;> simp [binary]
    have id := congrArg encode (actual.symm.trans same)
    simp only [identityLabels] at id
    exact False.elim (ca id)
  · have eq : binary op (word b) (word a) = binary op (word a) (word b) := by
      cases op <;> simp [binary,BitVec.and_comm,BitVec.or_comm]
    exact .swapped (ruleOf ba (eq.trans actual) cb ca) x y

def minor (v : Fin 8 → Bool) :=
  v 0 && v 1 || v 1 && v 2 || v 2 && v 3 || v 0 && v 4 || v 1 && v 5 ||
  v 2 && v 6 || v 3 && v 7 || v 4 && v 6 || v 5 && v 7 || v 7 && v 4
def inputAt (r : Nat) (i : Fin 8) := r.testBit i.val
theorem baseLow : ∀ (i : Fin 8) (r : Fin 256),
    (word (base i)).getLsbD r.val = inputAt r.val i := by decide +kernel
theorem goalLow : ∀ r : Fin 256, (word goal).getLsbD r.val = minor (inputAt r.val) := by decide +kernel
def highTarget (r : Nat) := minor (inputAt r) || inputAt r 0 || inputAt r 3
theorem highRows : highTarget 1 = true ∧ highTarget 8 = true ∧ highTarget 52 = false := by decide +kernel
theorem negAbsent : ∀ a c : Label, ~~~(word a) ≠ word c := by decide +kernel

/-- A lifted circuit over the listed 256-bit lower-cofactor values. A free first OR may
replace input 1 by true in the upper cofactor, and one fixed reader class may also supply
true. Each choice can be made independently at each use. -/
inductive Lift (p : Label) : Label → High → Prop where
  | var (i : Fin 8) : Lift p (base i) (baseHigh i)
  | inputOr : Lift p (base 1) 7
  | readerOr : Lift p p 7
  | gate {op a b c i j} : Lift p a i → Lift p b j →
      binary op (word a) (word b) = word c → c≠a → c≠b → Lift p c (combine op i j)

theorem lifted {p a v} (h : Lift p a v) : Realizes p a v := by
  induction h with
  | var i => exact .atom i
  | inputOr => exact .first
  | readerOr => exact .special
  | gate _ _ value a b left right => exact liftedGate left right value a b
theorem noLift (p : Label) : ¬Lift p goal 3 := fun h => impossible p (lifted h)
end PetersenReaderGrammar
#print axioms PetersenReaderGrammar.noLift
