import AbstractFileNode, { AbstractFileParams } from "./abstract";
import DirNode from "./directory";
import { FileTypes } from "./types";

export interface SymlinkParams extends AbstractFileParams { link: string; }

// Symlink for shortcuts
class SymlinkNode extends AbstractFileNode {
  link: string;
  readonly type = FileTypes.LINK;

  constructor(params: AbstractFileParams, parent: DirNode | null) {
    super(params, parent);
    this.link = params.link!;
  }

  public toObject = (): SymlinkParams => {
    return {
      name: this.name,
      link: this.link,
      type: FileTypes.LINK,
    }
  };
}

export default SymlinkNode;
