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
import SymlinkNode from "./classes/symlink";
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

interface WriteActionValues extends CommonActionValues {
  force?: boolean;
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
interface CopyMoveActionValue extends WriteActionValues { file: string; newLocation: string; newName?: string };
interface DeleteActionValue extends WriteActionValues   { file: string; };
interface UpdateActionValue extends WriteActionValues   { file: string; newData?: any; newName?: string };

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
  INVALID_FILE_NAME = 'invalid-file-name',
  INVALID_PATH_NAME = 'invalid-path-name',
};
export interface ActionLog {
  status: LogStatus;
  type: Action;
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
});

// stick to very basic names for now
const validateFileName = (name: string) => !!name.match(/^[A-Za-z0-9\-_\s.]+$/g)
const validatePath = (path: string) => !path.includes('//') && path.split('/').filter(v => !!v).every(f => validateFileName(f));

const moveFileAction = (state: SimulatedFileSystem, action: CopyAction | MoveAction) => {
  const srcFile = getFileFromPath(action.value.file, state.fileHierarchy) as DataNode;
  if (!srcFile) {
    return addNewLog(state, action, LogStatus.NO_SUCH_FILE);
  }
  const updatedFileName = action.value.newName || srcFile.name;
  if (!validateFileName(updatedFileName)) {
    return addNewLog(state, action, LogStatus.INVALID_FILE_NAME);
  }
  if(!validatePath(action.value.newLocation)) {
    return addNewLog(state, action, LogStatus.INVALID_PATH_NAME);
  }
  const destDirectory = getFileFromPath(action.value.newLocation, state.fileHierarchy);
  if (!(destDirectory instanceof DirNode)) {
    return addNewLog(state, action, LogStatus.ERROR);
  }
  if ((!destDirectory || !destDirectory.contents) && !action.value.confirm) {
    return addNewLog(state, action, LogStatus.NO_SUCH_DIRECTORY);
  }
  const existingFile = getFileFromPath(`${destDirectory?.getPath()}/${updatedFileName}`, state.fileHierarchy);
  if (existingFile) {
    if (!action.value.force) {
      return addNewLog(state, action, LogStatus.ALREADY_EXISTS);
    }
    destDirectory.contents = destDirectory.contents.filter(v => v !== existingFile);
    existingFile.parent = null;
  }
  const srcDirectory = srcFile.parent;
  let newFile: DirNode | DataNode | SymlinkNode = srcFile;
  if (Action.COPY) {
    newFile = initialiseFileFromObject({ ...srcFile.toObject(), name: updatedFileName, readonly: false });
  }
  newFile.parent = destDirectory as DirNode;
  newFile.name = updatedFileName;
  (destDirectory as DirNode).contents = [
    ...(destDirectory as DirNode).contents,
    newFile, // will have wrong parent at this point
  ];
  if (action.type === Action.MOVE && srcDirectory instanceof DirNode) {
    srcDirectory.contents = srcDirectory.contents?.filter(v => v !== srcFile);
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
      if (!validateFileName(action.value.newFile.name)) {
        return addNewLog(state, action, LogStatus.INVALID_FILE_NAME);
      }
      if(!validatePath(fileLocation.getPath())) {
        return addNewLog(state, action, LogStatus.INVALID_PATH_NAME);
      }
      const newFileName = `${action.value.location}/${action.value.newFile.name}`
      const existingFile = getFileFromPath(newFileName, fileLocation as DirNode);
      if (existingFile && !action.value.confirm) {
        return addNewLog(state, action, LogStatus.ALREADY_EXISTS);
      }
      if (fileLocation.isReadOnly()) {
        return addNewLog(state, action, LogStatus.UNAUTHORIZED);
      }
      fileLocation.addNewFile(action.value.newFile);

      return {
        ...state,
        fileHierarchy: refreshRoot(fileLocation),
      };
    case Action.COPY:
      if (!getFileFromPath(action.value.file, state.fileHierarchy)) {
        return addNewLog(state, action, LogStatus.NO_SUCH_FILE);
      }
      return moveFileAction(state, action);
    case Action.MOVE:
      const movedFile = getFileFromPath(action.value.file, state.fileHierarchy);
      if (!movedFile) {
        return addNewLog(state, action, LogStatus.NO_SUCH_FILE);
      }
      const newDirectory = getFileFromPath(action.value.newLocation, state.fileHierarchy);
      if (movedFile.isReadOnly() || newDirectory?.isReadOnly()) {
        return addNewLog(state, action, LogStatus.UNAUTHORIZED);
      }
      return moveFileAction(state, action);
    case Action.DELETE:
      if (!getFileFromPath(action.value.file, state.fileHierarchy)) {
        return addNewLog(state, action, LogStatus.NO_SUCH_FILE);
      }
      // TODO recycle bin?
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
      if (file.isReadOnly()) {
        return addNewLog(state, action, LogStatus.UNAUTHORIZED);
      }
      if (action.value.newData) {
        file.data = action.value.newData;
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
