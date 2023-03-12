import DataNode from "./data";
import DirNode from "./directory";
import SymlinkNode from "./symlink";

// TODO not importing in tests??
export enum FileTypes {
  DIR = 'DIR',
  DATA = 'DATA',
  LINK = 'LINK',
}

export type ValidFileNode = DataNode | SymlinkNode | DirNode;