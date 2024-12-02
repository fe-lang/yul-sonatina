object "Contract1" {
    code {
        let d := dataoffset("CONSTANT")
        let s := datasize("CONSTANT")
        codecopy(0, d, s)
    }

    data "CONSTANT" hex"4123"
}
