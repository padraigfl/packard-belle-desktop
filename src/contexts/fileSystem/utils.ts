import { AbstractFileParams } from "./classes/abstract";
import DataNode from "./classes/data";
import DirNode from "./classes/directory";
import SymlinkNode from "./classes/symlink";
import { FileTypes, ValidFileNode } from "./classes/types";

// default hierarchy
export const mntHierarchyNested = {
  name: '',
  contents: [{
    name: 'mnt',
    contents: [
      {
        name: 'c',
        contents: [
          { name: 'trash', contents: [] },
          {
            name: 'usr',
            contents: [
              {
                name: 'me',
                contents: [
                  {
                    name: 'desktop',
                    contents: [
                      { name: 'resume.txt', data: 'testingtest text text text' },
                      { name: 'My Computer',  type: FileTypes.LINK, link: '/mnt', special: 'My Computer' },
                      { name: 'Recycle Bin',  type: FileTypes.LINK, link: '/mnt/c/trash', special: 'Recycle Bin' }, 
                      { name: 'readme.html',  data: '<p>And the text is <b>BOLD</b> in this line</p>' },
                    ]
                  },
                  {
                    name: 'readonly',
                    contents: [
                      { name: 'file.txt', data: 'sometext'},
                      {
                        name: 'nested',
                        contents: [{ name: 'file.txt', data: 'sometext' }],
                      },
                    ],
                    readonly: true,
                  },
                  { name: 'readonly.txt', data: 'test', readonly: true },
                  { name: 'readme.html',  data: '<p>And the text is <b>BOLD</b> in this line</p>' },
                ]
              }
            ]
          },
          {
            name: 'windows',
            contents: [
              { name: 'Start Menu', contents: [ { name: 'Programs', contents: [] } ] }
            ]
          }
        ],
      },
    ],
  }],
};

// removes file from parent and returns root
export const deleteFile = (directory: DirNode, filePath: string) => {
  if (filePath.trim() === '/') {
    throw new Error('unauthorized');
  }
  const file = getFileFromPath(filePath, directory);
  if (!file) {
    throw new Error('no-such-file');
  }
  if (file && file?.parent) {
    file.parent.contents = (file.parent as DirNode)?.contents.filter(v => v !== file);
  }
  return getFileFromPath('/', directory) as DirNode;
}

export const getFileFromPath = (path: string, directory: DirNode): ValidFileNode | undefined => {
  let baseDirectory = directory;
  let trimmedPath = path.trim();

  // get root directory if path begins with '/'
  if (trimmedPath[0] === '/') {
    trimmedPath = trimmedPath.replace(/^\//, '');
    while (baseDirectory.parent && baseDirectory.parent.type === FileTypes.DIR) {
      baseDirectory = (baseDirectory.parent as DirNode);
    }
  }
  if (trimmedPath === '') {
    return baseDirectory;
  }
  const parsedPath = trimmedPath.split('/');
  let iterative: DirNode | SymlinkNode | DataNode | undefined = baseDirectory;
  for (const step of parsedPath) {
    if (iterative?.type === FileTypes.DIR) {
      iterative = (iterative as DirNode).contents.find(v => v.name === step);
    } else {
      return undefined;
    }
  }
  return iterative;
};

export const initialiseFileFromObject = (obj: AbstractFileParams, parent?: DirNode): DirNode | DataNode | SymlinkNode => {
  if (obj.type === FileTypes.DATA || obj.data) {
    return new DataNode(obj, parent || null);
  }
  if (obj.type === FileTypes.DIR || obj.contents) {
    return new DirNode(obj, parent || null);
  }
  if (obj.type === FileTypes.LINK || obj.link) {
    return new SymlinkNode(obj, parent || null);
  }
  throw Error('invalid file format');
}


// /* TODO: TEMP OPERATION FUNCTIONS, REPLACE WITH LODASH OR SIMILAR */
// export const getValueFromFileObject = (path: string, fileSystemObject: AbstractFileParams) => {
//   const parsedPath = path.split('/');
//   let iterative: AbstractFileParams | undefined = fileSystemObject;
//   for (const step of parsedPath) {
//     if (iterative?.contents) {
//       iterative = iterative.contents.find(v => v.name === step);
//     } else {
//       return undefined;
//     }
//   }
//   return iterative;
// };
// export const setValueInFileObject = (
//   path: string,
//   fileSystemObject: AbstractFileParams,
//   value: AbstractFileParams,
//   params?: { newFile?: boolean; needsExistingDirectories?: boolean }
// ) => {
//   const parsedPath = path.split('/');
//   let iterative: AbstractFileParams | undefined = fileSystemObject;
//   for (const step of parsedPath) {
//     const nextIteration = iterative?.contents?.find(v => v.name === step);
//     if (!nextIteration && params?.needsExistingDirectories) {
//       const newObject = { name: step, contents: [] };
//       iterative.contents = [ ...(iterative?.contents || []), newObject]
//       iterative = newObject;
//     }
//   }
//   const updateIdx = iterative.contents?.findIndex(v => v.name === value.name) || -1;
//   if (updateIdx !== -1) {
//     (iterative as any).contents[updateIdx] = params?.newFile
//       ? value
//       : { ...iterative?.contents?.[updateIdx], ...value}
//   }

//   return fileSystemObject;
// };


/* currently handled within class definitions */
// // functions for converting class into an object based structure, currently handled within the class
// const getSymlinkNodeObject = (symlink: SymlinkNode): SymlinkParams => {
//   const { name, type, readonly, customIcon, link } = symlink;
//   return { name, type, readonly, customIcon, link };
// };
// const getDataNodeObject = (dataNode: DataNode): DataParams => {
//   const { name, type, readonly, customIcon, data } = dataNode;
//   return { name, type, readonly, customIcon, data };
// };

// // For converting class based structure back to an object (e.g. for saving)
// export const getDirNodeObject = (directory: DirNode): DirectoryParams => {
//   const { name, type, readonly, customIcon, contents } = directory;
//   return {
//     name,
//     type,
//     readonly,
//     customIcon,
//     contents: contents.map(v => {
//       if (v.type === FileTypes.DIR) {
//         return getDirNodeObject(v as DirNode);
//       }
//       if (v.type === FileTypes.LINK) {
//         return getSymlinkNodeObject(v as SymlinkNode);
//       }
//       return getDataNodeObject(v as DataNode);
//     })
//   }
// };

