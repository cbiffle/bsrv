# vim:syntax=python:

bluespec_library('Board',
    sources = [
        'Board.bsv',
    ],
)

bluespec_verilog('examples',
    top = 'Examples.bsv',
    modules = [
        'mkBlinky',
    ],
    deps = [
        ':Board',
        '//hdl/examples:Blinky',
    ],
)

# Blinky design targets

yosys_design('blinky',
    top_module = 'mkBlinky',
    sources = [
        ':examples#mkBlinky',
    ],
    deps = [
        ':examples',
    ],
)

nextpnr_ice40_bitstream('blinky_icestick',
    env = 'icestick',
    design = ':blinky#json',
    deps = [
        ':blinky',
    ],
)
