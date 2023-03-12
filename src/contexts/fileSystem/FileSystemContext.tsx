import { useReducer } from "react";
import { createContext } from "react";
import { AbstractFileParams } from "./classes/abstract";
import DirNode from "./classes/directory";
import { getFileSystemInitialState, FileSystemAction, fileSystemReducer, SimulatedFileSystem, ActionLog } from "./filesystem";
import { mntHierarchyNested } from "./utils";

interface FileSystemContextType {
  fileHierarchy: DirNode,
  logs: { [actionId: string]: ActionLog }
  dispatch: any,
}
interface FileSystemContextProviderProps {
  customFileHierarchy: AbstractFileParams,
  children?: Element,
}

const FileSystemContext = createContext({
  ...getFileSystemInitialState(),
} as unknown as FileSystemContextType);

export const FileSystemContextProvider = (props: FileSystemContextProviderProps = { customFileHierarchy: mntHierarchyNested}) => {
  const [{ fileHierarchy, logs }, dispatch] = useReducer<
    (state: SimulatedFileSystem, action: FileSystemAction) => SimulatedFileSystem,
    SimulatedFileSystem
  >(fileSystemReducer, { fileHierarchy: new DirNode(props.customFileHierarchy), logs: {} }, v => v);

  return (
    <FileSystemContext.Provider
      value={{
        fileHierarchy,
        dispatch,
        logs,
      }}
    >
      {props.children}
    </FileSystemContext.Provider>
  );
}