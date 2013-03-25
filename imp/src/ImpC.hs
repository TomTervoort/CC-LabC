import CCO.Component  (printer, ioWrap)
import CCO.Imp        (parser, toCode)
import Control.Arrow  (arr, (>>>))

main = ioWrap (parser >>> arr toCode >>> printer)