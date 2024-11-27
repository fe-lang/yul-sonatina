object "Contract1" {
    code {
        function allocate(size) -> ptr {
            ptr := mload(0x40)
            if iszero(ptr) { ptr := 0x60 }
            mstore(0x40, add(ptr, size))
        }

        let size := datasize("Contract2")
        let offset := allocate(size)
        datacopy(offset, dataoffset("Contract2"), size)
        mstore(add(offset, size), 0x1234)
        pop(create(0, offset, add(size, 32)))

        size := datasize("Contract1_deployed")
        offset := allocate(size)
        datacopy(offset, dataoffset("Contract1_deployed"), size)
        return(offset, size)
    }

    data "Table2" hex"4123"

    object "Contract1_deployed" {
        code {
            function allocate(size) -> ptr {
                ptr := mload(0x40)
                if iszero(ptr) { ptr := 0x60 }
                mstore(0x40, add(ptr, size))
            }

            return(0, 0x20)
        }
    }

    object "Contract2" {
        code {
        }
    }
}
