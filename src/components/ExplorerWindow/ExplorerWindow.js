import React from "react";
import { WindowExplorer } from "packard-belle";
import * as icons from "../../icons";
import "./_styles.scss";
import Window from "../tools/Window";

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
const noop = () => {};

const Explorer = props => (
  <Window
    {...props}
    Component={WindowExplorer}
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
    menuOptions={buildMenu(props)}
  />
);

export default Explorer;

// initialHeight, initialWidth, title, icon, footer, id,
// onClose, onMaximize, isActive, explorerOptions, chidlren, data, customSelect, Component
