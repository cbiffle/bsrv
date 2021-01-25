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
        '../../BRAM2.v',
        '../../BRAM1Load.v',
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
        '//hdl/examples:Twisty5Soc',
    ],
)

yosys_design('twisty',
    top_module = 'mkTwisty',
    sources = [
        ':twisty_example#mkTwisty',
        '../../BRAM2Load.v',
        '../../BRAM1Load.v',
        '../../MakeReset.v',
        '../../SyncReset.v',
        '../../ResetInverter.v',
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

bluespec_verilog('examples',
    top = 'Examples.bsv',
    modules = [
        'mkDinky',
        'mkTangy',
    ],
    deps = [
        ':Board',
        '//hdl/examples:Dinky5Soc',
        '//hdl/examples:Tangy5Soc',
    ],
)

yosys_design('dinky',
    top_module = 'mkDinky',
    sources = [
        ':examples#mkDinky',
        '../../BRAM2.v',
        '../../BRAM1Load.v',
    ],
    deps = [
        ':examples',
    ],
)

nextpnr_ice40_bitstream('dinky_icestick',
    env = 'icestick',
    design = ':dinky#json',
    deps = [
        ':dinky',
    ],
)

yosys_design('tangy',
    top_module = 'mkTangy',
    sources = [
        ':examples#mkTangy',
        '../../BRAM2.v',
        '../../BRAM1.v',
    ],
    deps = [
        ':examples',
    ],
)

nextpnr_ice40_bitstream('tangy_icestick',
    env = 'icestick',
    design = ':tangy#json',
    deps = [
        ':tangy',
    ],
)

