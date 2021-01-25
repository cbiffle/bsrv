// ULX3S eval board support.

package Board;

// Hardware interface available to / expected from top-modules on the ULX3S
// board.
(* always_ready, always_enabled *)
interface Top;
    (* prefix = "ftdi" *)
    interface SerialPort serial;

    (* result = "led" *)
    method Bit#(8) leds;

    (* prefix = "" *)
    method Action buttons((* port = "btn" *) Bit#(6) state);

    (* prefix = "" *)
    method Action dip_switches((* port = "sw" *) Bit#(4) state);
endinterface

// Generic serial port interface, but missing the signals the ULX3S decided not
// to wire up (e.g. DCD).
//
// Note that the names of the transmit/receive signals are overridden and
// appear backwards. This is deliberate: the net names in the constraints file
// are intended to match the schematic, which uses FTDI-side naming for the
// UART nets. So "TXD" is our receive.
(* always_ready, always_enabled *)
interface SerialPort;
    (* result = "rxd" *)
    method bit tx;
    (* prefix = "" *)
    method Action rx((* port = "txd" *) bit data);
    (* prefix = "" *)
    method Action dtr_n((* port = "ndtr" *) bit state);
endinterface

// Don't care about the serial port? I can hook you up.
module mkDummySerialPort (SerialPort);
    method tx = 1;
    method rx(_) = noAction;
    method dtr_n(_) = noAction;
endmodule

endpackage
