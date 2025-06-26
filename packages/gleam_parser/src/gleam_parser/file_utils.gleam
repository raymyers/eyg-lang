@external(erlang, "file", "read_file")
@external(javascript, "./file_utils_ffi.mjs", "readFile")
pub fn read_file(path: String) -> Result(String, String)
