import DirNode from "../classes/directory";
import { FileTypes } from "../classes/types";
import { Action, fileSystemReducer, SimulatedFileSystem } from "../filesystem";
import { getFileFromPath, mntHierarchyNested } from "../utils"

describe('fileSystemReducer', () => {
  let state: SimulatedFileSystem;
  beforeAll(() => {
    state = {
      fileHierarchy: new DirNode(mntHierarchyNested),
      logs: {},
    };
  })
  it(Action.NEW, () => {
    const newSystem = fileSystemReducer(state, {
      type: Action.NEW,
      value: {
        actionId: 'abc',
        location: '/mnt/c/usr/me',
        newFile: {
          type: FileTypes.DATA,
          data: { text: 'this is the text' },
          name: 'testFile.txt',
        }
      },
    });
    expect(getFileFromPath('/mnt/c/usr/me/testFile.txt', newSystem.fileHierarchy)).toBeTruthy();
  });
  // copies file
  // fails to copy if duplicate
  // force override on copy
  it(Action.COPY, () => {
    const copySystem = fileSystemReducer(state, {
      type: Action.COPY,
      value: {
        file: '/mnt/c/usr/me/desktop/resume.txt',
        newLocation: '/mnt/c/usr/me',
        actionId: 'abcd',
      },
    });
    expect(getFileFromPath('/mnt/c/usr/me/resume.txt', copySystem.fileHierarchy)).toBeTruthy();
  });
  // delete
  // fails to delete if not exist
  // cant delete protected
  it(Action.DELETE, () => {});
  // file exists in new directory
  // file no longer exists in source directory
  // file can't be moved for various reasons (same name, protected)
  it(Action.MOVE, () => {});
  // old file no longer exists
  // new file exists
  // file can't be updated for various reasons (same name, protected)
  it(Action.UPDATE, () => {});
})