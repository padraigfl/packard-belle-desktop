import AbstractFileNode, { AbstractFileParams } from "./abstract";
import DirNode from "./directory";
import { FileTypes } from "./types";

export interface DataParams extends AbstractFileParams { data: any; }

// General data file node
class DataNode extends AbstractFileNode {
  static lostFilesDir = null; // new DirNode({ name: "LOST" }, null);
  data: any;
  readonly type = FileTypes.DATA;

  constructor(params: AbstractFileParams, parent: DirNode | null) {
    super(params, parent);
    if (!this.parent) {
      this.parent = DataNode.lostFilesDir;
    }
    this.data = params.data;
  }

  public toObject() {
    return {
      ...super.toObject(),
      type: FileTypes.DATA,
      data: this.data,
    }
  }
}

export default DataNode;
