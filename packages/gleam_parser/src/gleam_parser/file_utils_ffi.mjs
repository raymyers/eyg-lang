import { readFileSync } from "fs";
import { Ok, Error } from "../gleam.mjs";

export function readFile(path) {
  try {
    const content = readFileSync(path, "utf8");
    return new Ok(content);
  } catch (error) {
    return new Error(error.message);
  }
}