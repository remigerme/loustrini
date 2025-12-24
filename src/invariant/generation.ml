let gen_inv ctx env =
  Boolean.gen_inv ctx env
  @ Numeral.gen_inv ctx env Numeral.Mint
  @ Numeral.gen_inv ctx env Numeral.Mreal
