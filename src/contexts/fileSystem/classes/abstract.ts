/* Attempting to replicate a filesystem as a nested class */

import DirNode from "./directory";
import { FileTypes } from "./types";

export interface AbstractFileParams {
  name: string;
  contents?: AbstractFileParams[];
  type?: FileTypes;
  readonly?: boolean; // should cascade
  customIcon?: any;
  data?: any;
  link?: any;
  special?: any;
}

// Abstracted general class for all file operations
class AbstractFileNode implements AbstractFileParams {
  name: string;
  parent: DirNode | null;
  readonly?: boolean | undefined;
  customIcon?: any;
  type?: FileTypes;
  contents?: AbstractFileParams[] | undefined;

  constructor(params: AbstractFileParams, parent: DirNode | null) {
    this.parent = parent instanceof AbstractFileNode ? parent : null;
    this.name = params.name;
    this.readonly = params.readonly;
    this.customIcon = params.customIcon;
  }

  public isReadOnly = () => {
    let iterativeValue = this.readonly;
    let focusedNode = this as AbstractFileNode; // TODO revisti this override
    while (!iterativeValue && !!focusedNode?.parent) {
      focusedNode = focusedNode?.parent;
      iterativeValue = focusedNode?.isReadOnly();
    }
    return iterativeValue || false;
  }

  public getPath = (relativeNode?: AbstractFileNode) => {
    let path = this.name;
    let ancestor = this.parent;
    while (ancestor && ancestor !== relativeNode) {
      path = `${ancestor.name}/${path}`;
      ancestor = ancestor?.parent;
    }
    return path;
  }

  public toObject = () => {
    return { name: this.name };
  }

  public toString = () => {
    return JSON.stringify(this.toObject());
  }
}

export default AbstractFileNode;
