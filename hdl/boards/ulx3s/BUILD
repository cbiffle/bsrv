# vim:syntax=python:

bluespec_library('Board',
    sources = [
        'Board.bsv',
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

nextpnr_ecp5_bitstream('twisty_ulx3s',
    env = 'ulx3s',
    design = ':twisty#json',
    deps = [
        ':twisty',
    ],
)
