# vim:syntax=python:

bluespec_library('Board',
    sources = [
        'Board.bsv',
    ],
)

bluespec_verilog('corny_example',
    top = 'CornyExample.bsv',
    modules = [
        'mkCorny',
    ],
    deps = [
        ':Board',
        '//hdl/examples:Corny5Soc',
    ],
)

yosys_design('corny',
    top_module = 'mkCorny',
    sources = [
        ':corny_example#mkCorny',
        '../../support/BRAM2.v',
        '../../support/BRAM1Load.v',
    ],
    deps = [
        ':corny_example',
    ],
)

nextpnr_ice40_bitstream('corny_icestick',
    env = 'icestick',
    design = ':corny#json',
    deps = [
        ':corny',
    ],
)

bluespec_verilog('twisty_example',
    top = 'TwistyExample.bsv',
    modules = [
        'mkTwisty',
    ],
    deps = [
        ':Board',
        '//hdl/fams/ice40:Ice40Pll',
        '//hdl/examples:Twisty5Soc',
    ],
)

yosys_design('twisty',
    top_module = 'mkTwisty',
    sources = [
        ':twisty_example#mkTwisty',
        '../../support/BRAM2Load.v',
        '../../support/BRAM1Load.v',
        '../../support/MakeReset.v',
        '../../support/SyncReset.v',
        '../../support/ResetInverter.v',
    ],
    deps = [
        ':twisty_example',
    ],
)

nextpnr_ice40_bitstream('twisty_icestick',
    env = 'icestick',
    design = ':twisty#json',
    deps = [
        ':twisty',
    ],
)

bluespec_verilog('dinky_example',
    top = 'DinkyExample.bsv',
    modules = [
        'mkDinky',
    ],
    deps = [
        ':Board',
        '//hdl/examples:Dinky5Soc',
    ],
)

yosys_design('dinky',
    top_module = 'mkDinky',
    sources = [
        ':dinky_example#mkDinky',
        '../../support/BRAM2Load.v',
        '../../support/BRAM1Load.v',
    ],
    deps = [
        ':dinky_example',
    ],
)

nextpnr_ice40_bitstream('dinky_icestick',
    env = 'icestick',
    design = ':dinky#json',
    deps = [
        ':dinky',
    ],
)

bluespec_verilog('tangy_example',
    top = 'TangyExample.bsv',
    modules = [
        'mkTangy',
    ],
    deps = [
        ':Board',
        '//hdl/examples:Tangy5Soc',
    ],
)

yosys_design('tangy',
    top_module = 'mkTangy',
    sources = [
        ':tangy_example#mkTangy',
        '../../support/BRAM2.v',
        '../../support/BRAM1.v',
    ],
    deps = [
        ':tangy_example',
    ],
)

nextpnr_ice40_bitstream('tangy_icestick',
    env = 'icestick',
    design = ':tangy#json',
    deps = [
        ':tangy',
    ],
)
