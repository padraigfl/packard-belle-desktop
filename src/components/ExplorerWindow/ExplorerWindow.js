import React from "react";
import { WindowExplorer } from "packard-belle";
import Window from "../tools/Window";
import * as icons from "../../icons";
import "./_styles.scss";

const noop = () => {};

export const buildMenu = props => [
  {
    title: "File",
    options: [
      { title: "Open", isDisabled: true },
      { title: "Close", onClick: () => props.onClose(props) }
    ]
  },
  {
    title: "Help",
    options: [{ title: `About ${props.title}`, isDisabled: true }]
  }
];

const Explorer = props => (
  <Window
    {...props}
    initialHeight={props.initialHeight || 200}
    initialWidth={props.initialWidth || 200}
  >
    {rnd => (
      <WindowExplorer
        title={props.title}
        icon={props.icon}
        footer={[
          { text: "needs 100% width height" },
          { text: "overflow control" }
        ]}
        onClose={() => props.onClose(props)}
        onMinimize={() => {}}
        onRestore={rnd.restore}
        onMaximize={rnd.maximize}
        changingState={rnd.state.isDragging || rnd.state.isResizing}
        className={props.isActive && "Window--active"}
        menuOptions={buildMenu(props)}
        explorerOptions={[
          {
            icon: icons.back,
            title: "Back",
            onClick: noop
          },
          {
            icon: icons.forward,
            title: "Forward",
            onClick: noop
          },
          {
            icon: icons.upDir,
            title: "Up",
            onClick: noop
          },
          {
            icon: icons.cut,
            title: "Cut",
            onClick: noop
          },
          {
            icon: icons.copy,
            title: "Copy",
            onClick: noop
          },
          {
            icon: icons.delete,
            title: "Delete",
            onClick: noop
          },
          {
            icon: icons.properties,
            title: "Properties",
            onClick: noop
          },
          {
            icon: icons.views,
            title: "Views"
          }
        ]}
      >
        {props.title} and the content goes here
      </WindowExplorer>
    )}
  </Window>
);

export default Explorer;
