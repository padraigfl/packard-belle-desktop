// Notes on structure:
// - uses hierarchy of nested class instances built from a highly typed object
// - retains the ability to revert back to an object via a secondary function
// - symlink directories need to be hardcoded and will be broken by moving files
// - reducer heavily checks to ensure all changes do not break the file hierarchy
// - UI can contain a LOST folder for handling additional lost items if desired
// 
// TODO
// - Need to handle trash on multiple drives? A drive instantiation process?
// - error handling to pass messaging to system

import { AbstractFileParams } from "./classes/abstract";
import DataNode from "./classes/data";
import DirNode from "./classes/directory";
import { FileTypes, ValidFileNode } from "./classes/types";
import { deleteFile, getFileFromPath, initialiseFileFromObject, mntHierarchyNested } from "./utils";

export enum Action {
  NEW     = 'NEW_FILE',
  MOVE    = 'MOVE_FILE',
  COPY    = 'COPY_FILE',
  DELETE  = 'DELETE_FILE',
  UPDATE  = 'UPDATE_FILE',
};

interface CommonActionValues {
  actionId: string; // for validating behaviour issues, logging
  confirm?: boolean; // forces behaviour (e.g. "are you sure you want to overwrite")
}
interface NewActionValue extends CommonActionValues {
  newFile: {
    name: string; // contents, data, reference link
  } & (
    { type: FileTypes.DATA; data: any }
    | { type: FileTypes.DIR; contents: AbstractFileParams[] }
    | { type: FileTypes.LINK; link: string }
  )
  location: string;
};
interface CopyMoveActionValue extends CommonActionValues { file: string; newLocation: string; };
interface DeleteActionValue extends CommonActionValues   { file: string; };
interface UpdateActionValue extends CommonActionValues   { file: string; newData?: any; newName?: string };

interface NewAction     { type: Action.NEW;     value: NewActionValue; };
interface CopyAction    { type: Action.COPY;    value: CopyMoveActionValue; };
interface MoveAction    { type: Action.MOVE;    value: CopyMoveActionValue; }
interface DeleteAction  { type: Action.DELETE;  value: DeleteActionValue; }
interface UpdateAction  { type: Action.UPDATE;  value: UpdateActionValue; }

export type FileSystemAction = NewAction | CopyAction | MoveAction | DeleteAction | UpdateAction

export enum LogStatus {
  SUCCESS = 'success',
  ERROR = 'error',
  PROCESSING = 'processing',
  CONFIRMATION_REQUIRED = 'confirmation-required',
  NO_SUCH_DIRECTORY = 'no-such-directory',
  NO_SUCH_FILE = 'no-such-file',
  ALREADY_EXISTS = 'already-exists',
  UNAUTHORIZED = 'unauthorized',
};
export interface ActionLog {
  status: LogStatus;
}
export interface SimulatedFileSystem {
  fileHierarchy: DirNode;
  logs: { [actionId: string]: ActionLog }
};

const addNewLog = (state: SimulatedFileSystem, action: FileSystemAction, status: LogStatus) => ({
  ...state,
  logs: {
    [action.value.actionId]: { status, type: action.type }
  }
})

const moveFileAction = (state: SimulatedFileSystem, action: CopyAction | MoveAction) => {
  const srcFile = getFileFromPath(action.value.file, state.fileHierarchy) as DataNode;
  if (!srcFile) {
    return addNewLog(state, action, LogStatus.NO_SUCH_FILE);
  }
  const destDirectory = getFileFromPath(action.value.newLocation, state.fileHierarchy);
  if ((!destDirectory || !destDirectory.contents) && !action.value.confirm) {
    return addNewLog(state, action, LogStatus.NO_SUCH_DIRECTORY);
  }
  const copyFile = initialiseFileFromObject(srcFile.toObject());
  copyFile.parent = destDirectory as DirNode;
  (destDirectory as DirNode).contents = [
    ...(destDirectory as DirNode).contents,
    copyFile, // will have wrong parent at this point
  ];
  if (action.type === Action.MOVE && srcFile.parent) {
    (srcFile.parent as DirNode).contents = srcFile.parent?.contents?.filter(v => v === srcFile);
  }

  return {
    ...state,
    fileHierarchy: new DirNode(state.fileHierarchy.toObject()),
  };
}

const refreshRoot = (file: ValidFileNode) => {
  return new DirNode((getFileFromPath('/', (file.parent as DirNode)) as DirNode).toObject())
}

export function fileSystemReducer(state: SimulatedFileSystem, action: FileSystemAction ): SimulatedFileSystem {
  switch(action.type) {
    case Action.NEW:
      const fileLocation = getFileFromPath(action.value.location, state.fileHierarchy) as DirNode;
      if (!fileLocation || !fileLocation.contents) {
        return addNewLog(state, action, LogStatus.NO_SUCH_DIRECTORY);
      }
      const newFileName = `${action.value.location}/${action.value.newFile.name}`
      const existingFile = getFileFromPath(newFileName, fileLocation as DirNode);
      if (existingFile && !action.value.confirm) {
        return addNewLog(state, action, LogStatus.CONFIRMATION_REQUIRED);
      }
      fileLocation.addNewFile(action.value.newFile);

      return {
        ...state,
        fileHierarchy: refreshRoot(fileLocation),
      };
    case Action.COPY:
      return moveFileAction(state, action);
    case Action.MOVE:
      return moveFileAction(state, action);
    case Action.DELETE:
      // TODO recycle bin?
      if (getFileFromPath(action.value.file, state.fileHierarchy)) {
        return addNewLog(state, action, LogStatus.NO_SUCH_FILE);
      }
      try {
        const updatedFileObj = (deleteFile(state.fileHierarchy, action.value.file)).toObject()
        return {
          ...state,
          fileHierarchy: new DirNode(updatedFileObj),
        };
      } catch (e) {
        return addNewLog(state, action, LogStatus.NO_SUCH_FILE);
      }
    case Action.UPDATE:
      const file = getFileFromPath(action.value.file, state.fileHierarchy) as DataNode;
      if (!file || file?.type !== FileTypes.DATA) {
        return addNewLog(state, action, LogStatus.NO_SUCH_FILE);
      }

      if (action.value.newName) {
        if (file?.parent?.contents.some(v => (v.name === action.value.newName && v !== file))) {
          return addNewLog(state, action, LogStatus.ALREADY_EXISTS);
        } else {
          file!.name = action.value.newName;
        }
      } else if (action.value.newData) {
        file.data = {
          ...file.data,
          ...action.value.newData,
        };
      }

      return {
        ...state,
        fileHierarchy: refreshRoot(file.parent as DirNode),
      };
    default:
      return state;
  }
}

export const getFileSystemInitialState = (hierarchy: AbstractFileParams = mntHierarchyNested) => ({
  fileHierarchy: new DirNode(hierarchy),
  logs: {},
});
