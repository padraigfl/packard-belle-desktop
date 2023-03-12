import { LogStatus } from "../filesystem";
import { initialiseFileFromObject } from "../utils";
import AbstractFileNode, { AbstractFileParams } from "./abstract";
import DataNode, { DataParams } from "./data";
import SymlinkNode, { SymlinkParams } from "./symlink";
import { FileTypes } from "./types";

export interface DirectoryParams extends AbstractFileParams { contents: (DataParams | SymlinkParams | DirectoryParams)[]; }

// Directory for containing other files
class DirNode extends AbstractFileNode {
  contents: (DirNode | SymlinkNode | DataNode)[];
  readonly type = FileTypes.DIR;

  constructor(params: AbstractFileParams, parent: DirNode | null = null) {
    super(params, parent);
    const currentNode = this;
    this.contents = params.contents
      ? params.contents.map((v: AbstractFileParams) => {
        if (v.contents) {
          return new DirNode(v, currentNode);
        };
        if (v.link) {
          return new SymlinkNode(v, currentNode);
        }
        if (v.data) {
          return new DataNode(v, currentNode);
        }
        throw Error("Invalid file specication"); // TODO: create broken file type?
      })
      : [];
  }

  toObject = (): DirectoryParams => {
    return {
      name: this.name,
      type: FileTypes.DIR,
      contents: this.contents.map(v => v.toObject()),
    };
  }

  addNewFile = (params: AbstractFileParams): any => {
    const sameNameFile = this.contents.find(v => v.name === params.name);
    if (sameNameFile && (
      params.type === FileTypes.DIR
        ? sameNameFile.type === FileTypes.DIR
        : sameNameFile.type !== FileTypes.DIR
      )
    ) {
      throw new Error(LogStatus.ALREADY_EXISTS)
    }
    const newFile = initialiseFileFromObject(params, this);
    this.contents.push(newFile);
    return newFile;
  }
}

export default DirNode;
