# vim:syntax=python:

bluespec_library('Board',
    sources = [
        'Board.bsv',
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

